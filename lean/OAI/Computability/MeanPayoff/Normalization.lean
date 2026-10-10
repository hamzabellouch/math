import OAI.Computability.MeanPayoff.ArenaParsing

namespace OAI

section
namespace MeanPayoff.TreeDevice.Normalize
open BinaryData
abbrev Count := Median.Count
abbrev Edge := EdgeRead.Edge
abbrev Arena := ArenaRead.Arena

def countData := listTree Median.unitData
def edgeData := EdgeRead.edgeData
def edgesData := listTree edgeData
def ownersData := listTree boolData
def arenaData := ArenaRead.arenaData

def edge (z : Count × Edge) : Edge := (z.2.1,(z.2.2.1,Scale.transform (z.2.2.2,z.1)))
noncomputable def sourceDevice : Device (product countData edgeData) countData (fun z : Count × Edge => z.2.1) :=
  compose (second countData edgeData) (first countData (product countData wordData))
noncomputable def moreDevice : Device (product countData edgeData) (product countData wordData) (fun z : Count × Edge => z.2.2) :=
  compose (second countData edgeData) (second countData (product countData wordData))
noncomputable def targetDevice : Device (product countData edgeData) countData (fun z : Count × Edge => z.2.2.1) :=
  compose moreDevice (first countData wordData)
noncomputable def weightDevice : Device (product countData edgeData) wordData (fun z : Count × Edge => z.2.2.2) :=
  compose moreDevice (second countData wordData)
noncomputable def scaleArgsDevice : Device (product countData edgeData) (product wordData countData)
    (fun z : Count × Edge => (z.2.2.2,z.1)) := fanout weightDevice (first countData edgeData)
noncomputable def scaleDevice : Device (product countData edgeData) wordData (fun z : Count × Edge => Scale.transform (z.2.2.2,z.1)) :=
  @compose (Count × Edge) (SignedBits.Word × Count) SignedBits.Word (product countData edgeData)
    (product wordData countData) wordData (fun z => (z.2.2.2,z.1)) Scale.transform scaleArgsDevice Scale.transformDevice
noncomputable def edgeDevice : Device (product countData edgeData) edgeData edge :=
  fanout sourceDevice (fanout targetDevice scaleDevice)

def arena (z : Arena) : Arena := (z.1,(z.2.1,z.2.2.map (fun e => edge (z.1,e))))
noncomputable def nDevice : Device arenaData countData (fun z : Arena => z.1) := first countData (product ownersData edgesData)
noncomputable def restDevice : Device arenaData (product ownersData edgesData) (fun z : Arena => z.2) := second countData (product ownersData edgesData)
noncomputable def ownersDevice : Device arenaData ownersData (fun z : Arena => z.2.1) := compose restDevice (first ownersData edgesData)
noncomputable def edgesDevice : Device arenaData edgesData (fun z : Arena => z.2.2) := compose restDevice (second ownersData edgesData)
noncomputable def mapDevice : Device arenaData edgesData (fun z : Arena => z.2.2.map (fun e => edge (z.1,e))) :=
  compose (fanout nDevice edgesDevice) (EnvMap.device edgeDevice)
noncomputable def arenaDevice : Device arenaData arenaData arena :=
  fanout nDevice (fanout ownersDevice mapDevice)

def read (xs : List Bool) := arena (ArenaRead.read xs)
noncomputable def device : Device (listTree boolData) arenaData read := compose ArenaRead.device arenaDevice

def word (G : Game) (e : Fin G.m) := Scale.transform (EdgeRead.encodedWord (G.weight e),List.replicate G.n ())
def encodedEdge (G : Game) (e : Fin G.m) : Edge :=
  (List.replicate (G.tail e).val (),(List.replicate (G.head e).val (),word G e))

theorem word_val (G : Game) (e : Fin G.m) : (word G e).val=transformed G e := by
  simp only [word,Scale.transform_val,List.length_replicate,EdgeRead.encodedWord_val,transformed]

theorem edge_exact (G : Game) (e : Fin G.m) :
    edge (List.replicate G.n (),EdgesRead.lower ((G.tail e).val,(G.head e).val,G.weight e))=encodedEdge G e := rfl

theorem exact (G : Game) : read (input G) =
    (List.replicate G.n (),(List.ofFn G.maxOwner,List.ofFn (encodedEdge G))) := by
  rw [read,ArenaRead.game_exact]
  simp only [arena,BinaryInput.lower,List.map_ofFn,Function.comp_def,edge_exact]

theorem source_linear : LinearCost sourceDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem target_linear : LinearCost targetDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem weight_linear : LinearCost weightDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem scaleArgs_linear : LinearCost scaleArgsDevice := LinearCost.fanout weight_linear (LinearCost.first _ _)
theorem scale_polynomial : PolynomialCost scaleDevice :=
  PolynomialCost.compose scaleArgs_linear.polynomial Scale.transform_polynomial
theorem edge_polynomial : PolynomialCost edgeDevice :=
  PolynomialCost.fanout source_linear.polynomial (PolynomialCost.fanout target_linear.polynomial scale_polynomial)
theorem n_linear : LinearCost nDevice := LinearCost.first _ _
theorem rest_linear : LinearCost restDevice := LinearCost.second _ _
theorem owners_linear : LinearCost ownersDevice := LinearCost.compose rest_linear (LinearCost.first _ _)
theorem edges_linear : LinearCost edgesDevice := LinearCost.compose rest_linear (LinearCost.second _ _)
theorem map_polynomial : PolynomialCost mapDevice :=
  PolynomialCost.compose (LinearCost.fanout n_linear edges_linear).polynomial (EnvMap.polynomial edge_polynomial)
theorem arena_polynomial : PolynomialCost arenaDevice :=
  PolynomialCost.fanout n_linear.polynomial (PolynomialCost.fanout owners_linear.polynomial map_polynomial)

theorem polynomial : PolynomialCost device := PolynomialCost.compose ArenaRead.polynomial arena_polynomial
end MeanPayoff.TreeDevice.Normalize
namespace MeanPayoff.TreeDevice.Adjacency
open BinaryData
abbrev Count := Median.Count
abbrev Edge := EdgeRead.Edge
abbrev Edges := List Edge

def countData := listTree Median.unitData
def edgeData := EdgeRead.edgeData
def edgesData := listTree edgeData

def test (p : Count × Edge) := CountTest.equal (p.1,p.2.1)
noncomputable def testArgsDevice : Device (product countData edgeData) (product countData countData)
    (fun p : Count × Edge => (p.1,p.2.1)) :=
  fanout (first countData edgeData) (compose (second countData edgeData) (first countData Graph.edgeData))
noncomputable def testDevice : Device (product countData edgeData) Compare.bitTree test :=
  @compose (Count × Edge) (Count × Count) Bool (product countData edgeData) (product countData countData)
    Compare.bitTree (fun p => (p.1,p.2.1)) CountTest.equal testArgsDevice CountTest.device

def select (z : Count × Edges) : List Graph.Edge :=
  (z.2.filter (fun e => test (z.1,e))).map Prod.snd
noncomputable def selectDevice : Device (product countData edgesData) (listTree Graph.edgeData) select :=
  compose (EnvFilter.device testDevice) (Map.device (second countData Graph.edgeData))

def defaultEdge : Graph.Edge := ([],Median.zeroWord)
def nonempty (xs : List Graph.Edge) : Graph.Edges := (xs.headD defaultEdge,xs.tail)
noncomputable def nonemptyDevice : Device (listTree Graph.edgeData) Graph.edgesData nonempty :=
  fanout (Head.device Graph.edgeData defaultEdge) (Tail.device Graph.edgeData)

def vertex (edges : Edges) (p : Count × Bool) : Graph.Vertex :=
  (p.2,nonempty (select (p.1,edges)))
abbrev Args := Edges × (Count × Bool)
def argsData := product edgesData (product countData boolData)
noncomputable def localDevice : Device argsData (product countData boolData) (fun p : Args => p.2) := second edgesData (product countData boolData)
noncomputable def ownerDevice : Device argsData Compare.bitTree (fun p : Args => p.2.2) :=
  (compose (compose localDevice (second countData boolData)) Multiply.rawTest).extFun (by intro p; rfl)
noncomputable def addressDevice : Device argsData countData (fun p : Args => p.2.1) :=
  compose localDevice (first countData boolData)
noncomputable def selectArgsDevice : Device argsData (product countData edgesData) (fun p : Args => (p.2.1,p.1)) :=
  fanout addressDevice (first edgesData (product countData boolData))
noncomputable def selectedDevice : Device argsData (listTree Graph.edgeData) (fun p : Args => select (p.2.1,p.1)) :=
  @compose Args (Count × Edges) (List Graph.Edge) argsData (product countData edgesData)
    (listTree Graph.edgeData) (fun p => (p.2.1,p.1)) select selectArgsDevice selectDevice
noncomputable def vertexDevice : Device argsData Graph.vertexData (fun p : Args => vertex p.1 p.2) :=
  fanout ownerDevice (compose selectedDevice nonemptyDevice)

theorem test_exact (G : Game) (v : Fin G.n) (e : Fin G.m) :
    test (List.replicate v.val (),Normalize.encodedEdge G e)=decide (G.tail e=v) := by
  rw [test,CountTest.equal_eq]
  simp only [Normalize.encodedEdge,List.length_replicate]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact Fin.ext h.symm
  · intro h; exact congrArg Fin.val h.symm

theorem select_exact (G : Game) (v : Fin G.n) :
    select (List.replicate v.val (),List.ofFn (Normalize.encodedEdge G)) =
      (Graph.outList G v).map (Graph.codeEdge G (Normalize.word G)) := by
  simp only [select,List.ofFn_eq_map,List.filter_map,List.map_map,Function.comp_def,test_exact]
  rfl

theorem vertex_exact (G : Game) (v : Fin G.n) :
    vertex (List.ofFn (Normalize.encodedEdge G)) (List.replicate v.val (),G.maxOwner v) =
      Graph.codeVertex G (Normalize.word G) v := by
  rw [vertex,select_exact]
  have h := Graph.outList_ne_nil G v
  rw [show Graph.outList G v=Graph.firstEdge G v::(Graph.outList G v).tail from (List.cons_head_tail h).symm]
  rfl

theorem testArgs_linear : LinearCost testArgsDevice :=
  LinearCost.fanout (LinearCost.first _ _) (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _))
theorem test_polynomial : PolynomialCost testDevice := PolynomialCost.compose testArgs_linear.polynomial CountTest.polynomial
theorem select_polynomial : PolynomialCost selectDevice :=
  PolynomialCost.compose (EnvFilter.polynomial test_polynomial) (PolynomialCost.map (LinearCost.second _ _).polynomial)
theorem nonempty_linear : LinearCost nonemptyDevice := LinearCost.fanout (LinearCost.head _ _) (LinearCost.tail _)
theorem local_linear : LinearCost localDevice := LinearCost.second _ _
theorem owner_linear : LinearCost ownerDevice :=
  LinearCost.compose (LinearCost.compose local_linear (LinearCost.second _ _)) Multiply.rawTest_linear
theorem address_linear : LinearCost addressDevice := LinearCost.compose local_linear (LinearCost.first _ _)
theorem selectArgs_linear : LinearCost selectArgsDevice := LinearCost.fanout address_linear (LinearCost.first _ _)
theorem selected_polynomial : PolynomialCost selectedDevice := PolynomialCost.compose selectArgs_linear.polynomial select_polynomial
theorem vertex_polynomial : PolynomialCost vertexDevice :=
  PolynomialCost.fanout owner_linear.polynomial (PolynomialCost.compose selected_polynomial nonempty_linear.polynomial)
end MeanPayoff.TreeDevice.Adjacency
namespace MeanPayoff.TreeDevice.Rows
open BinaryData
abbrev Edge := EdgeRead.Edge
abbrev Edges := List Edge
abbrev Count := Median.Count
abbrev Arena := ArenaRead.Arena
abbrev State := StreamFold.State Edges Graph.Vertex (List Bool)

def ownersData := listTree boolData
def countData := listTree Median.unitData
def edgesData := listTree EdgeRead.edgeData
def outputData := listTree Graph.vertexData
def rowArgsData := product edgesData ownersData
def rowOutputData := product Graph.vertexData ownersData
def stateData := StreamFold.stateData edgesData Graph.vertexData ownersData

def count (xs : List Bool) : Count := xs.map (fun _ => ())
noncomputable def countDevice : Device ownersData countData count :=
  Map.device (constant boolData Median.unitData ())

theorem count_eq (xs : List Bool) : count xs = List.replicate xs.length () := by simp [count]

def row (p : Edges × List Bool) : Graph.Vertex × List Bool :=
  (Adjacency.vertex p.1 (count p.2.tail,p.2.headD false),p.2.tail)
noncomputable def streamDevice : Device rowArgsData ownersData (fun p : Edges × List Bool => p.2) := second edgesData ownersData
noncomputable def remainderDevice : Device rowArgsData ownersData (fun p : Edges × List Bool => p.2.tail) :=
  compose streamDevice (Tail.device boolData)
noncomputable def addressDevice : Device rowArgsData countData (fun p : Edges × List Bool => count p.2.tail) :=
  compose remainderDevice countDevice
noncomputable def ownerDevice : Device rowArgsData boolData (fun p : Edges × List Bool => p.2.headD false) :=
  compose streamDevice (Head.device boolData false)
noncomputable def vertexArgsDevice : Device rowArgsData Adjacency.argsData
    (fun p : Edges × List Bool => (p.1,(count p.2.tail,p.2.headD false))) :=
  fanout (first edgesData ownersData) (fanout addressDevice ownerDevice)
noncomputable def vertexDevice : Device rowArgsData Graph.vertexData
    (fun p : Edges × List Bool => Adjacency.vertex p.1 (count p.2.tail,p.2.headD false)) :=
  compose vertexArgsDevice Adjacency.vertexDevice
noncomputable def rowDevice : Device rowArgsData rowOutputData row := fanout vertexDevice remainderDevice

def descending (edges : Edges) : List Bool → List Graph.Vertex
  | [] => []
  | b::bs => Adjacency.vertex edges (List.replicate bs.length (),b)::descending edges bs

theorem fold_exact (edges : Edges) (owners : List Bool) (acc : List Graph.Vertex) :
    Fold.fold (StreamFold.step row) (edges,(acc,owners)) (List.replicate owners.length ()) =
      (edges,((descending edges owners).reverse++acc,[])) := by
  induction owners generalizing acc with
  | nil => simp [Fold.fold,descending]
  | cons b bs ih =>
    simp only [List.length_cons,List.replicate_succ,Fold.fold,List.foldl_cons]
    change Fold.fold (StreamFold.step row) (StreamFold.step row ((edges,(acc,b::bs)),())) (List.replicate bs.length ())= _
    simp only [StreamFold.step,row,List.tail_cons,List.headD_cons,count_eq]
    rw [ih]
    simp [descending,List.reverse_cons,List.append_assoc]

theorem descending_ofFn (edges : Edges) {n : ℕ} (f : Fin n → Bool) :
    (descending edges (List.ofFn f).reverse).reverse=
      List.ofFn (fun i => Adjacency.vertex edges (List.replicate i.val (),f i)) := by
  induction n with
  | zero => simp [descending]
  | succ n ih =>
    rw [List.ofFn_succ_last,List.reverse_append]
    simp only [List.singleton_append,descending,List.length_reverse,List.length_ofFn,List.reverse_cons,List.reverse_nil,List.nil_append]
    rw [ih,List.ofFn_succ_last]
    rfl

def build (z : Arena) : List Graph.Vertex :=
  (Fold.fold (StreamFold.step row) (z.2.2,([],z.2.1.reverse)) z.1).2.1
noncomputable def restDevice : Device ArenaRead.arenaData (product ownersData edgesData) (fun z : Arena => z.2) := second countData (product ownersData edgesData)
noncomputable def edgesDevice : Device ArenaRead.arenaData edgesData (fun z : Arena => z.2.2) := compose restDevice (second ownersData edgesData)
noncomputable def ownersDevice : Device ArenaRead.arenaData ownersData (fun z : Arena => z.2.1) := compose restDevice (first ownersData edgesData)
noncomputable def reversedDevice : Device ArenaRead.arenaData ownersData (fun z : Arena => z.2.1.reverse) :=
  compose ownersDevice (Lists.reverseDevice boolData)
noncomputable def stateDevice : Device ArenaRead.arenaData stateData (fun z : Arena => (z.2.2,([],z.2.1.reverse))) :=
  fanout edgesDevice (compose reversedDevice (Lists.nilPrefix ownersData Graph.vertexData))
noncomputable def initDevice : Device ArenaRead.arenaData (product stateData countData)
    (fun z : Arena => ((z.2.2,([],z.2.1.reverse)),z.1)) :=
  fanout stateDevice (first countData (product ownersData edgesData))
noncomputable def resultDevice : Device stateData outputData (fun s : State => s.2.1) :=
  compose (second edgesData (product outputData ownersData)) (first outputData ownersData)
noncomputable def foldedDevice : Device (product stateData countData) outputData
    (fun z : State × Count => (Fold.fold (StreamFold.step row) z.1 z.2).2.1) :=
  @compose (State × Count) State (List Graph.Vertex) (product stateData countData) stateData outputData
    (fun z => Fold.fold (StreamFold.step row) z.1 z.2) (fun s => s.2.1)
    (Fold.device (StreamFold.stepDevice rowDevice)) resultDevice
noncomputable def buildDevice : Device ArenaRead.arenaData outputData build :=
  @compose Arena (State × Count) (List Graph.Vertex) ArenaRead.arenaData (product stateData countData) outputData
    (fun z => ((z.2.2,([],z.2.1.reverse)),z.1)) (fun z => (Fold.fold (StreamFold.step row) z.1 z.2).2.1)
    initDevice foldedDevice

def read (xs : List Bool) : List Graph.Vertex := build (Normalize.read xs)
noncomputable def device : Device (listTree boolData) outputData read := compose Normalize.device buildDevice

theorem build_exact (G : Game) :
    build (List.replicate G.n (),(List.ofFn G.maxOwner,List.ofFn (Normalize.encodedEdge G))) =
      Graph.codeVertices G (Normalize.word G) := by
  have hf := fold_exact (List.ofFn (Normalize.encodedEdge G)) (List.ofFn G.maxOwner).reverse []
  simp only [List.length_reverse,List.length_ofFn] at hf
  change (Fold.fold (StreamFold.step row) (List.ofFn (Normalize.encodedEdge G),([], (List.ofFn G.maxOwner).reverse)) (List.replicate G.n ())).2.1 = _
  rw [hf]
  simp only [List.append_nil,descending_ofFn,Graph.codeVertices]
  apply congrArg List.ofFn
  funext v
  exact Adjacency.vertex_exact G v

theorem exact (G : Game) : read (input G) = Graph.codeVertices G (Normalize.word G) := by
  rw [read,Normalize.exact,build_exact]

theorem count_polynomial : PolynomialCost countDevice := PolynomialCost.map (LinearCost.constant _ _ _).polynomial
theorem stream_linear : LinearCost streamDevice := LinearCost.second _ _
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose stream_linear (LinearCost.tail _)
theorem address_polynomial : PolynomialCost addressDevice := PolynomialCost.compose remainder_linear.polynomial count_polynomial
theorem owner_linear : LinearCost ownerDevice := LinearCost.compose stream_linear (LinearCost.head _ _)
theorem vertexArgs_polynomial : PolynomialCost vertexArgsDevice :=
  PolynomialCost.fanout (LinearCost.first _ _).polynomial (PolynomialCost.fanout address_polynomial owner_linear.polynomial)
theorem vertex_polynomial : PolynomialCost vertexDevice := PolynomialCost.compose vertexArgs_polynomial Adjacency.vertex_polynomial
theorem row_polynomial : PolynomialCost rowDevice := PolynomialCost.fanout vertex_polynomial remainder_linear.polynomial

theorem fold_polynomial : PolynomialCost (Fold.device (StreamFold.stepDevice rowDevice)) := by
  apply StreamFold.polynomial rowDevice row_polynomial
  intro edges owners
  change treeSize (ownersData owners.tail)≤treeSize (ownersData owners)
  cases owners <;> simp only [ownersData,List.tail_nil,List.tail_cons,listTree,treeSize_pair] <;> omega

theorem rest_linear : LinearCost restDevice := LinearCost.second _ _
theorem edges_linear : LinearCost edgesDevice := LinearCost.compose rest_linear (LinearCost.second _ _)
theorem owners_linear : LinearCost ownersDevice := LinearCost.compose rest_linear (LinearCost.first _ _)
theorem reversed_polynomial : PolynomialCost reversedDevice := PolynomialCost.compose owners_linear.polynomial (PolynomialCost.reverse _)
theorem state_polynomial : PolynomialCost stateDevice :=
  PolynomialCost.fanout edges_linear.polynomial (PolynomialCost.compose reversed_polynomial (LinearCost.nilPrefix _ _).polynomial)
theorem init_polynomial : PolynomialCost initDevice := PolynomialCost.fanout state_polynomial (LinearCost.first _ _).polynomial
theorem result_linear : LinearCost resultDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem folded_polynomial : PolynomialCost foldedDevice := PolynomialCost.compose fold_polynomial result_linear.polynomial
theorem build_polynomial : PolynomialCost buildDevice := PolynomialCost.compose init_polynomial folded_polynomial

theorem polynomial : PolynomialCost device := PolynomialCost.compose Normalize.polynomial build_polynomial
end MeanPayoff.TreeDevice.Rows
end

end OAI
