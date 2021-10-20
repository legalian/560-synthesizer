use std::collections::HashSet;
use std::collections::HashMap;
use std::collections::VecDeque;
use chrono::{NaiveDateTime};

use std::env;
use std::fs::File;

use petgraph::{Graph,Directed};
use petgraph::graph::{Edges,EdgeReference};
use petgraph::prelude::{NodeIndex,EdgeIndex};
use petgraph::visit::EdgeRef;

use serde::{Serialize,Deserialize};

use std::vec::IntoIter;
use std::io::Read;
use csv::{Reader,Writer};

use std::rc::{Rc};
use std::cmp::Ordering;
use std::fs;
use std::str::FromStr;

type Tname = usize;
type Cname = usize;

enum Key {
    Asc(Cname),
    Desc(Cname)
}
enum Col {
    Named(Cname),
    GC(Box<Gc>)
}
type Gc = (Agg,Cname);
type Pairs = Vec<Pair>;
type Pair = (Cname,Cname);
type Pred = Vec<Prim>;
enum Prim {
    Const(Col,Binop),
    IsNull(Cname),
    IsNotNull(Cname)
}
enum Agg {
    Max,
    Min,
}
enum Binop {
    Eq,
    Lt,
    Lteq,
    Gt,
    Gteq,
    Neq
}

enum Tier1Table {
    Order(Tier2Table,Vec<Key>),
    N(Tier2Table)
}
use Tier1Table::{*};
enum Tier2Table {
    Project(Tier3Table,Vec<Cname>),
    N(Tier3Table)
}
use Tier2Table::{*};
enum Tier3Table {
    Select(Tier4Table,Pred),
    N(Tier4Table)
}
use Tier3Table::{*};
enum Tier4Table {
    Named(Tname),
    Group( Box<Tier3Table>, Vec<Cname>, Vec<Gc>),
    Join( Box<Tier4Table>, Box<Tier4Table>, Pairs),
    LeftJoin( Box<Tier4Table>, Box<Tier3Table>, Pair)
}
use Tier4Table::{*};


trait Query {
    fn evaluate(&self,tables:&Vec<Table>)->Table;
    fn totop(self)->Tier1Table;
}

impl Query for Tier1Table {
    fn evaluate(&self,tables:&Vec<Table>)->Table {
        match self {
            Tier1Table::Order(sq,keys) => {
                let subq = sq.evaluate(tables);
                let mut indecies:Vec<usize> = (0..subq.rows).collect();
                indecies.sort_by(|x,y|{
                    for key in keys {
                        match key {
                            Key::Asc(col)=>{
                                if compare_table_values(&subq,*col,*x,&subq,*col,*y) {continue;}
                                return if compare_table_values_lt(&subq,*col,*x,&subq,*col,*y)
                                    {Ordering::Less} else {Ordering::Greater};
                            },
                            Key::Desc(col)=>{
                                if compare_table_values(&subq,*col,*x,&subq,*col,*y) {continue;}
                                return if compare_table_values_lt(&subq,*col,*x,&subq,*col,*y)
                                    {Ordering::Greater} else {Ordering::Less};
                            }
                        }
                    }
                    return Ordering::Equal;
                });
                let mut schema = get_table_schema(&subq);
                for a in indecies.iter() {add_row_table(&mut schema,&subq,*a);}
                return schema;
            }
            Tier1Table::N(sq) => sq.evaluate(tables)
        }
    }
    fn totop(self)->Tier1Table {self}
}
impl Query for Tier2Table {
    fn evaluate(&self,tables:&Vec<Table>)->Table {
        match self {
            Tier2Table::Project(sq,chosencols) => {
                let subq = sq.evaluate(tables);
                return Table {
                    columns:chosencols.iter().map(|x|subq.columns[*x].clone()).collect(),
                    rows:subq.rows
                };
            }
            Tier2Table::N(sq) => sq.evaluate(tables)
        }
    }
    fn totop(self)->Tier1Table {Tier1Table::N(self)}
}
impl Query for Tier3Table {
    fn evaluate(&self,tables:&Vec<Table>)->Table {
        match self {
            Tier3Table::Select(sq,criteria) => {
                let subq = sq.evaluate(tables);
                let mut schema = get_table_schema(&subq);
                //TODO
                return schema;
            }
            Tier3Table::N(sq) => sq.evaluate(tables)
        }
    }
    fn totop(self)->Tier1Table {Tier1Table::N(Tier2Table::N(self))}
}
impl Query for Tier4Table {
    fn evaluate(&self,tables:&Vec<Table>)->Table {
        match self {
            Tier4Table::Named(tn)=>tables[*tn].clone(),
            Tier4Table::Group(sq,groupby,agg)=>{
                let subq = sq.evaluate(tables);
                let mut schema = get_table_schema(&subq);
                for row in 0..subq.rows {
                    let mut found = false;
                    for lessrow in 0..schema.rows {
                        let mut samerec = true;
                        for factor in groupby.iter() {
                            if !compare_table_values(&schema,*factor,lessrow,&subq,*factor,row) {samerec=false;}
                        }
                        if samerec {
                            found = true;
                            let mut firstit = true;//there's some weird niche SQL semantics that i'm emulating here
                            for (ag,agcol) in agg.iter().rev() {
                                if match ag {
                                    Agg::Max=>compare_table_values_lt(&schema,*agcol,lessrow,&subq,*agcol,row),
                                    Agg::Min=>compare_table_values_lt(&subq,*agcol,row,&schema,*agcol,lessrow)
                                } {
                                    if firstit {
                                        for col in 0..subq.columns.len() {
                                            move_table_values(&mut schema,col,lessrow,&subq,col,row);
                                        }
                                    } else {
                                        move_table_values(&mut schema,*agcol,lessrow,&subq,*agcol,row);
                                    }
                                }
                                firstit = false;
                            }
                            break;
                        }
                    }
                    if !found {
                        add_row_table(&mut schema,&subq,row);
                    }
                }
                return schema;
            },
            Tier4Table::Join( sq1, sq2, ps)=>{
                let subq1 = sq1.evaluate(tables);
                let subq2 = sq2.evaluate(tables);
                let mut lside = get_table_schema(&subq1);
                let mut rside = get_table_schema(&subq2);
                for a in 0..subq1.rows {
                    for b in 0..subq2.rows {
                        if ps.iter().all(|(c1,c2)|compare_table_values(&subq1,*c1,a,&subq2,*c2,b)) {
                            add_row_table(&mut lside,&subq1,a);
                            add_row_table(&mut rside,&subq2,b);
                        }
                    }
                }
                return table_glue(lside,rside);
            },
            Tier4Table::LeftJoin( sq1, sq2, ps)=>{
                let subq1 = sq1.evaluate(tables);
                let subq2 = sq2.evaluate(tables);
                let (c1,c2) = ps;
                let mut lside = get_table_schema(&subq1);
                let mut rside = get_table_schema(&subq2);
                for a in 0..subq1.rows {
                    let mut foundone = false;
                    for b in 0..subq2.rows {
                        if compare_table_values(&subq1,*c1,a,&subq2,*c2,b) {
                            add_row_table(&mut lside,&subq1,a);
                            add_row_table(&mut rside,&subq2,b);
                            foundone = true;
                        }
                    }
                    if !foundone {
                        add_row_table(&mut lside,&subq1,a);
                        add_null_row(&mut rside);
                    }
                }
                return table_glue(lside,rside);
            }
        }
    }
    fn totop(self)->Tier1Table {Tier1Table::N(Tier2Table::N(Tier3Table::N(self)))}
}





















#[derive(Debug,Clone)]
enum Column {
    String(Vec<Option<String>>),
    Numeric(Vec<Option<f64>>),
    Time(Vec<Option<NaiveDateTime>>)
}
enum ColumnPair<'a> {
    String(&'a Vec<Option<String>>,&'a Vec<Option<String>>),
    Numeric(&'a Vec<Option<f64>>,&'a Vec<Option<f64>>),
    Time(&'a Vec<Option<NaiveDateTime>>,&'a Vec<Option<NaiveDateTime>>)
}
fn columns_same_type<'a>(a:&'a Column,b:&'a Column)->Option<ColumnPair<'a>> {
    match (a,b) {
        (Column::String(a),Column::String(b))=>Some(ColumnPair::String(a,b)),
        (Column::Numeric(a),Column::Numeric(b))=>Some(ColumnPair::Numeric(a,b)),
        (Column::Time(a),Column::Time(b))=>Some(ColumnPair::Time(a,b)),
        _=>None
    }
}
enum ColumnPairMut<'a> {
    String(&'a mut Vec<Option<String>>,&'a Vec<Option<String>>),
    Numeric(&'a mut Vec<Option<f64>>,&'a Vec<Option<f64>>),
    Time(&'a mut Vec<Option<NaiveDateTime>>,&'a Vec<Option<NaiveDateTime>>)
}
fn columns_same_type_mut<'a>(a:&'a mut Column,b:&'a Column)->Option<ColumnPairMut<'a>> {
    match (a,b) {
        (Column::String(a),Column::String(b))=>Some(ColumnPairMut::String(a,b)),
        (Column::Numeric(a),Column::Numeric(b))=>Some(ColumnPairMut::Numeric(a,b)),
        (Column::Time(a),Column::Time(b))=>Some(ColumnPairMut::Time(a,b)),
        _=>None
    }
}
fn compare_table_values_full<'a>(a:&'a Table,b:&'a Table)->bool {
    if a.columns.len() != b.columns.len() || a.rows != b.rows {return false;}
    a.columns.iter().zip(b.columns.iter()).all(|(cola,colb)|{
        match columns_same_type(&cola,&colb) {
            None=>panic!("incorrectly typed comparison"),
            Some(ColumnPair::String(ac,bc)) => ac.iter().zip(bc.iter()).all(|(a,b)|a==b),
            Some(ColumnPair::Numeric(ac,bc)) => ac.iter().zip(bc.iter()).all(|(a,b)|a==b),
            Some(ColumnPair::Time(ac,bc)) => ac.iter().zip(bc.iter()).all(|(a,b)|a==b)
        }
    })
}
fn compare_table_values<'a>(a:&'a Table,ac:usize,ai:usize,b:&'a Table,bc:usize,bi:usize)->bool {
    match columns_same_type(&a.columns[ac],&b.columns[bc]) {
        None=>panic!("incorrectly typed comparison"),
        Some(ColumnPair::String(ac,bc)) => ac[ai]==bc[bi],
        Some(ColumnPair::Numeric(ac,bc)) => ac[ai]==bc[bi],
        Some(ColumnPair::Time(ac,bc)) => ac[ai]==bc[bi]
    }
}
fn compare_table_values_lt<'a>(a:&'a Table,ac:usize,ai:usize,b:&'a Table,bc:usize,bi:usize)->bool {
    match columns_same_type(&a.columns[ac],&b.columns[bc]) {
        None=>panic!("incorrectly typed comparison"),
        Some(ColumnPair::String(ac,bc)) => ac[ai]<bc[bi],
        Some(ColumnPair::Numeric(ac,bc)) => ac[ai]<bc[bi],
        Some(ColumnPair::Time(ac,bc)) => ac[ai]<bc[bi]
    }
}
fn move_table_values<'a>(a:&'a mut Table,ac:usize,ai:usize,b:&'a Table,bc:usize,bi:usize) {
    match columns_same_type_mut(& mut a.columns[ac],&b.columns[bc]) {
        None=>panic!("incorrectly typed assignment"),
        Some(ColumnPairMut::String(ac,bc)) => ac[ai]=bc[bi].clone(),
        Some(ColumnPairMut::Numeric(ac,bc)) => ac[ai]=bc[bi],
        Some(ColumnPairMut::Time(ac,bc)) => ac[ai]=bc[bi]
    }
}
#[derive(Debug, Clone)]
struct Table {
    columns:Vec<Column>,
    rows:usize
}
fn get_table_schema(t:&Table)->Table {
    return Table {
        columns:t.columns.iter().map(|x|match x {
            Column::String(_)=>Column::String(vec![]),
            Column::Numeric(_)=>Column::Numeric(vec![]),
            Column::Time(_)=>Column::Time(vec![]),
        }).collect(),
        rows:0
    }
}
fn table_glue(a:Table,b:Table)->Table {
    if a.rows != b.rows {panic!("Tried to combine two tables with different numbers of rows")}
    return Table {
        columns:a.columns.into_iter().chain(b.columns.into_iter()).collect(),
        rows:a.rows
    }
}
fn add_row_table(a:&mut Table,b:&Table,c:usize) {
    for column in 0..a.columns.len() {
        match columns_same_type_mut(&mut a.columns[column],&b.columns[column]) {
            None=>panic!("Tried to add row to table of incorrect schema"),
            Some(ColumnPairMut::String(ac,bc)) => ac.push(bc[c].clone()),
            Some(ColumnPairMut::Numeric(ac,bc)) => ac.push(bc[c]),
            Some(ColumnPairMut::Time(ac,bc)) => ac.push(bc[c])
        }
    }
    a.rows+=1;
}
fn add_null_row(a:&mut Table) {
    for column in 0..a.columns.len() {
        match &mut a.columns[column] {
            Column::String(ac) => ac.push(None),
            Column::Numeric(ac) => ac.push(None),
            Column::Time(ac) => ac.push(None)
        }
    }
    a.rows+=1;
}




















struct Pairing {
    source_col:usize,
    dest_col:usize,
    to:Vec<Vec<usize>>
}
struct LifeTimeLessEdgeRef {
    weight:Rc<Pairing>,
    id:EdgeIndex,
    source:NodeIndex,
    target:NodeIndex
}
fn remove_lifetime(a:EdgeReference<Rc<Pairing>>)->LifeTimeLessEdgeRef {
    return LifeTimeLessEdgeRef {
        weight:a.weight().clone(),
        id:a.id(),
        source:a.source(),
        target:a.target()
    }
}
type LinkGraph = Graph<usize,Rc<Pairing>,Directed>;
pub struct BreadthFirstExpand {
    queue: VecDeque<(NodeIndex,Option<(EdgeIndex,usize)>)>,
    graph: LinkGraph,
    next: Option<(IntoIter<LifeTimeLessEdgeRef>,Option<(EdgeIndex,usize)>)>,
}
impl Iterator for BreadthFirstExpand {
    type Item = ();
    fn next(&mut self) -> Option<Self::Item>  {
        loop {
            match &mut self.next {
                None=>match self.queue.pop_front(){
                    None=>{return None;}
                    Some((nx,prev))=>{
                        let a:Vec<_> = self.graph.edges(nx).map(|x|remove_lifetime(x)).collect();
                        self.next=Some((a.into_iter(),prev));
                        continue;
                    }
                }
                Some((x,prev))=>match x.next() {
                    None => {self.next=None;continue;}
                    Some(y) => {
                        if Some((y.id,y.weight.source_col)) == *prev {continue;}
                        self.queue.push_back((y.target,Some((y.id,y.weight.dest_col))));
                        return Some(());
                    }
                }
            }
        }
    }
}






#[derive(Clone,Copy)]
enum RowMappingQuality {
    EqualFooting,
    LeftMoreEmpty,
    RightMoreEmpty
}
struct RowMapping {
    ranges:Vec<Option<Vec<usize>>>
}
fn extract_comparisons(tables:&Vec<Table>)->LinkGraph {
    let mut deps = Graph::<usize,std::rc::Rc<Pairing>,Directed>::new();
    for ind in 0..tables.len() {deps.add_node(ind);}
    for ind1 in deps.node_indices() {
        let tab1 = &tables[deps[ind1]];
        for ind2 in deps.node_indices() {
            if ind2>ind1 {continue;}
            let tab2 = &tables[deps[ind2]];
            for (icol1,col1) in tab1.columns.iter().enumerate() {
                for (icol2,col2) in tab2.columns.iter().enumerate() {
                    if icol1==icol2 && ind1==ind2 {continue;}
                    if let Some((forward,backward)) = match columns_same_type(col1,col2) {
                        Some(ColumnPair::Numeric(a,b))=>create_bi_pairing(a,b),
                        Some(ColumnPair::String(a,b))=>create_bi_pairing(a,b),
                        Some(ColumnPair::Time(a,b))=>create_bi_pairing(a,b),
                        None=>None
                    } {
                        deps.add_edge(ind1,ind2,Rc::new(Pairing {
                            source_col:icol1,dest_col:icol2,to:forward
                        }));
                        deps.add_edge(ind2,ind1,Rc::new(Pairing {
                            source_col:icol2,dest_col:icol1,to:backward
                        }));
                    }
                }
            }
        }
    } deps
}
fn create_bi_pairing<'a,T:PartialEq>(target:&'a [Option<T>],source:&'a [Option<T>])->Option<(Vec<Vec<usize>>,Vec<Vec<usize>>)> {
    let ab = create_pairing(target,source);
    if ab.iter().all(|x|x.len()==0) {return None}
    let ba = create_pairing(source,target);
    return Some((ab,ba));
}
fn create_pairing<'a,T:PartialEq>(target:&'a [Option<T>],source:&'a [Option<T>])->Vec<Vec<usize>> {
    let mut outp = Vec::new();
    for t in target {
        let mut rv = Vec::new();
        if None!=*t {
            for j in 0..source.len() {
                if *t==source[j] { rv.push(j); }
            }
        }
        outp.push(rv);
    } outp
}
fn compare_columns<'a,T:PartialEq>(target:&'a [Option<T>],source:&'a [Option<T>])->Option<RowMapping> {
    let mut outp = Vec::new();
    for t in target {
        if let None=t {
            outp.push(None);
            continue;
        }
        let mut rv = Vec::new();
        for j in 0..source.len() {
            if *t==source[j] {
                rv.push(j);
            }
        }
        if rv.len()==0 {return None}
        outp.push(Some(rv));
    } Some(RowMapping {
        ranges:outp
    })
}
fn translate_map_across_pair(map:RowMapping,pair:Pairing)->Option<RowMapping> {
    let mut outp = Vec::new();
    for range in map.ranges {
        if let Some(r)=range {
            let mut rv = Vec::new();
            for val in r {
                for p in pair.to[val].iter() {
                    rv.push(*p);
                }
            }
            if rv.len()==0 {return None}
            outp.push(Some(rv));
        } else {
            outp.push(None);
        }
    }
    return Some(RowMapping {ranges:outp})
}
fn concatenate_pairings(a:Pairing,b:Pairing)->Pairing {
    let mut res = Vec::new();
    for ato in a.to {
        let mut rv = Vec::new();
        for at in ato {
            for bt in b.to[at].iter() {
                rv.push(*bt);
            }
        }
        res.push(rv);
    }
    return Pairing {
        to:res,
        source_col:a.source_col,
        dest_col:b.dest_col
    }
}
fn compare_mappings<'a,T:PartialEq>(a:RowMapping,b:RowMapping)->Option<(RowMapping,RowMappingQuality)> {
    let mut outp = Vec::new();
    let mut quality = RowMappingQuality::EqualFooting;
    if a.ranges.len()!=b.ranges.len() {panic!("Two mappings of different sizes should never arise.");}
    for lm in a.ranges.iter().zip(b.ranges.iter()) {
        outp.push(match (lm,quality) {
            ((None,None),_) => None,
            ((Some(_),None),RowMappingQuality::LeftMoreEmpty) => return None,//Outer joins are not allowed in our DSL for good reason
            ((None,Some(_)),RowMappingQuality::RightMoreEmpty) => return None,//Outer joins are not allowed in our DSL for good reason
            ((Some(a),None),_) => {
                quality=RowMappingQuality::RightMoreEmpty;Some(a.clone())
            },
            ((None,Some(b)),_) => {
                quality=RowMappingQuality::LeftMoreEmpty;Some(b.clone())
            },
            ((Some(a),Some(b)),_) => {
                let mut rv = Vec::new();
                let mut i=0;let mut j=0;
                while i<a.len() && j<b.len() {//each range in a rowmapping is sorted; this block calculates the intersection
                    if a[i]==b[j] {
                        rv.push(a[i]);
                        i+=1;j+=1;
                    } else if a[i]<b[i] {i+=1;} else {j+=1}
                }
                if rv.len()==0 {return None}
                Some(rv)
            },
        });
    }
    return Some((RowMapping {ranges:outp},quality))
}




// struct PartialSolutionManager {
//     Vec<Vec<>> solutions
// }


























#[derive(Debug, Serialize, Deserialize)]
enum ColumnSchema {
    String,
    Numeric,
    Time(String)
}
#[derive(Debug, Serialize, Deserialize)]
struct TableSchema {
    name:String,
    columns:Vec<(String,ColumnSchema)>
}
#[derive(Debug, Serialize, Deserialize)]
struct TestCaseSchema {
    inputs:Vec<TableSchema>,
    output:Vec<(String,ColumnSchema)>
}

#[derive(Debug)]
struct Example {
    inputs: Vec<Table>,
    output: Table,
    basepath: String
}

fn fit_examples(_schema:&TestCaseSchema,_examples: &Vec<Example>)->Tier1Table {
    return Named(1).totop()
}







fn test_fit(schema:&TestCaseSchema,examples: &Vec<Example>,expr:&Tier1Table) {
    for example in examples.iter() {
        let comparison:Table = expr.evaluate(&example.inputs);
        if !compare_table_values_full(&comparison,&example.output) {
            let comparefile = format!("{}actual.csv",example.basepath);
            write_file(comparefile.clone(),&schema.output,&comparison);
            panic!("fit wasn't valid for example. Saved actual result to {}",comparefile);
        }
    }
}
fn read_table(filepath:String,schema:&Vec<(String,ColumnSchema)>)->Table {
    let file = File::open(filepath.clone()).expect(format!("File not found: {}",filepath).as_str());
    let (cols,fmt) : (Vec<_>,Vec<_>) = schema.iter().map(|(_,u)|match u{
        ColumnSchema::String=>(Column::String(vec![]),None),
        ColumnSchema::Numeric=>(Column::Numeric(vec![]),None),
        ColumnSchema::Time(fmt)=>(Column::Time(vec![]),Some(fmt))
    }).unzip();
    let mut tab = Table {columns: cols,rows:0};
    for result in Reader::from_reader(file).records() {
        tab.rows+=1;
        for (ind,rec) in result.unwrap().iter().enumerate() {
            let trimrec = rec.trim();
            match &mut tab.columns[ind] {
                Column::String(v)=>{
                    v.push(if trimrec.len()==0 {None} else {Some(String::from(trimrec))})
                }
                Column::Numeric(v)=>{
                    v.push(if trimrec.len()==0 {None} else {Some(f64::from_str(trimrec).expect("CSV column doesn't have proper numeric type"))})
                }
                Column::Time(v)=>{
                    v.push(if trimrec.len()==0 {None} else {Some(NaiveDateTime::parse_from_str("23:56:04", fmt[ind].unwrap()).expect("CSV column doens't have proper time format"))})
                }
            }
        }
    } tab
}
fn write_file(filepath:String,schema:&Vec<(String,ColumnSchema)>,table:&Table) {
    let mut wtr = Writer::from_path(filepath).expect("Could not write to output file");
    for i in 0..table.rows {
        let row:Vec<String> = table.columns.iter().map(|x|match x {
            Column::Numeric(v)=>v[i].map(|y|format!("{}",y)).unwrap_or(String::from("")),
            Column::String(v)=>v[i].clone().unwrap_or(String::from("")),
            Column::Time(v)=>v[i].map(|y|format!("{}",y.format(match &schema[i].1 {
                ColumnSchema::Time(fmt)=>&fmt,
                _=>"%Y-%m-%d %H:%M:%S"
            }))).unwrap_or(String::from(""))
        }).collect();
        wtr.write_record(&row).expect("Could not write record to file");
    }
    wtr.flush().expect("Could not flush to output file");
}
fn main() {
    match env::args_os().nth(1) {
        None => {
            println!("please specify which test case should be attempted.");
            println!("available test cases:");
            for path in fs::read_dir("./testcases_v1/").unwrap() {
                let unwr = path.unwrap();
                if unwr.metadata().unwrap().file_type().is_dir() {
                    println!("\t{}",unwr.path().components().last().unwrap().as_os_str().to_str().unwrap());
                }
            }
        },
        Some(file_path) => {
            let patstr = file_path.to_str().unwrap();
            match fs::read_dir(format!("./testcases_v1/{}",patstr)) {
                Ok(iter)=>{
                    let mut fileschema = File::open(format!("./testcases_v1/{}/schema.json",patstr)).unwrap();
                    let mut dataschema = String::new();
                    fileschema.read_to_string(&mut dataschema).unwrap();
                    let schema:TestCaseSchema = serde_json::from_str(&dataschema).expect("JSON was not well-formatted");
                    let examples:Vec<Example> = iter.filter_map(|x|{
                        let y=x.unwrap();
                        if !y.metadata().unwrap().file_type().is_dir() {return None}
                        let ypath = y.path();
                        let ycomp = ypath.components().last().unwrap().as_os_str().to_str().unwrap();
                        return Some(Example {
                            inputs: schema.inputs.iter().map(|sch|read_table(format!("./testcases_v1/{}/{}/input_tables/{}.csv",patstr,ycomp,sch.name),&sch.columns)).collect(),
                            output: read_table(format!("./testcases_v1/{}/{}/output_table.csv",patstr,ycomp),&schema.output),
                            basepath: format!("./testcases_v1/{}/{}/",patstr,ycomp)
                        })
                    }).collect();
                    let fit = fit_examples(&schema,&examples);
                    test_fit(&schema,&examples,&fit);
                },
                Err(_)=>{
                    println!("cannot read testcase directory")
                }
            }
        }
    }
}

