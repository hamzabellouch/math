import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.BoolPrograms
import OAI.Combinatorics.ThinTrees.Continuation.BitBound
import OAI.Combinatorics.ThinTrees.Encoding.GreedyTree
import OAI.Combinatorics.ThinTrees.Sparsification.Realization

namespace OAI

/-! Greedy realization. -/

section

namespace AlgorithmicThinTrees.GreedyTree.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Finset StrongThinTree
open GraphStack
local notation "X" => NaturalPolynomial.variable

structure Subgraph where
  graph : Graph
  A : Finset (Fin graph.m)

def Subgraph.bits (s : Subgraph) := List.ofFn (fun e => decide (e ∈ s.A))
def subgraphCode (s : Subgraph) : Word := prodCode graphCode boolsCode (s.graph,s.bits)
abbrev subgraphView : Realizes subgraphCode (prodCode graphCode boolsCode) (fun s => (s.graph,s.bits)) :=
  (identity (prodCode graphCode boolsCode)).reindex subgraphCode (fun s => (s.graph,s.bits)) (fun _ => rfl)
private instance poly_subgraphView : PolyTime subgraphView := by
  unfold subgraphView
  apply poly_reindex

abbrev subgraphGraph := subgraphView.then (first graphCode boolsCode)
abbrev subgraphBits := subgraphView.then (second graphCode boolsCode)
abbrev subgraphN : Realizes subgraphCode natCode (fun s => s.graph.n) := subgraphGraph.then numVertices
private instance poly_subgraphN : PolyTime subgraphN := by
  unfold subgraphN
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · unfold numVertices
    apply poly_then

abbrev subgraphM : Realizes subgraphCode natCode (fun s => s.graph.m) := subgraphGraph.then numEdges

lemma subgraph_length (s : Subgraph) :
    (subgraphCode s).length=2*(graphCode s.graph).length+1+3*s.graph.m := by
  simp only [subgraphCode,prodCode_length,Subgraph.bits,bools_ofFn_length]

abbrev SEdge := Σ s : Subgraph, Fin s.graph.m
abbrev sedgeCode := finFamilyCode subgraphCode (fun s : Subgraph => s.graph.m)
abbrev sedgeContext : Realizes sedgeCode subgraphCode (fun s : SEdge => s.1) := familyFirst
abbrev sedgeIndex : Realizes sedgeCode natCode (fun s : SEdge => s.2.val) := familyIndex

def selected : Realizes sedgeCode boolCode (fun s => decide (s.2 ∈ s.1.A)) :=
  ((sedgeIndex.both (sedgeContext.then subgraphBits)).then (getD boolCode false)).congr
    (fun s => getD_ofFn _ s.2 false)
instance poly_selected : PolyTime selected := by unfold selected; apply poly_congr

structure ReachState where
  subgraph : Subgraph
  U : Finset (Fin subgraph.graph.n)

def ReachState.bits (s : ReachState) := List.ofFn (fun v => decide (v ∈ s.U))
def reachCode (s : ReachState) : Word := prodCode subgraphCode boolsCode (s.subgraph,s.bits)
abbrev reachView : Realizes reachCode (prodCode subgraphCode boolsCode) (fun s => (s.subgraph,s.bits)) :=
  (identity (prodCode subgraphCode boolsCode)).reindex reachCode (fun s => (s.subgraph,s.bits)) (fun _ => rfl)
private instance poly_reachView : PolyTime reachView := by
  unfold reachView
  apply poly_reindex

abbrev reachSubgraph := reachView.then (first subgraphCode boolsCode)
abbrev reachBits := reachView.then (second subgraphCode boolsCode)
abbrev reachN : Realizes reachCode natCode (fun s => s.subgraph.graph.n) := reachSubgraph.then subgraphN
private instance poly_reachN : PolyTime reachN := by
  unfold reachN
  apply poly_then

abbrev reachM : Realizes reachCode natCode (fun s => s.subgraph.graph.m) := reachSubgraph.then subgraphM
abbrev Vertex := Σ s : ReachState, Fin s.subgraph.graph.n
abbrev vertexCode := finFamilyCode reachCode (fun s : ReachState => s.subgraph.graph.n)
abbrev vertexContext : Realizes vertexCode reachCode (fun v : Vertex => v.1) := familyFirst
abbrev vertexIndex : Realizes vertexCode natCode (fun v : Vertex => v.2.val) := familyIndex

def reached : Realizes vertexCode boolCode (fun v => decide (v.2 ∈ v.1.U)) :=
  ((vertexIndex.both (vertexContext.then reachBits)).then (getD boolCode false)).congr
    (fun v => getD_ofFn _ v.2 false)
instance poly_reached : PolyTime reached := by unfold reached; apply poly_congr

abbrev Arc := Σ v : Vertex, Fin v.1.subgraph.graph.m
abbrev arcCode := finFamilyCode vertexCode (fun v : Vertex => v.1.subgraph.graph.m)
abbrev arcVertex : Realizes arcCode vertexCode (fun a : Arc => a.1) := familyFirst
abbrev arcNumber : Realizes arcCode natCode (fun a : Arc => a.2.val) := familyIndex
abbrev arcState := arcVertex.then vertexContext

def arcSubedge : Realizes arcCode sedgeCode (fun a => ⟨a.1.1.subgraph,a.2⟩) :=
  ((arcState.then reachSubgraph).both arcNumber).changeOutput sedgeCode
    (fun a => ⟨a.1.1.subgraph,a.2⟩) (fun _ => rfl)
instance poly_arcSubedge : PolyTime arcSubedge := by unfold arcSubedge; apply poly_changeOutput

def arcEdge : Realizes arcCode GraphStack.edgeCode (fun a => ⟨a.1.1.subgraph.graph,a.2⟩) :=
  ((arcState.then reachSubgraph |>.then subgraphGraph).both arcNumber).changeOutput
    GraphStack.edgeCode (fun a => ⟨a.1.1.subgraph.graph,a.2⟩) (fun _ => rfl)
instance poly_arcEdge : PolyTime arcEdge := by unfold arcEdge; apply poly_changeOutput
abbrev arcLeft := arcEdge.then edgeLeft
abbrev arcRight := arcEdge.then edgeRight

def leftReached : Realizes arcCode boolCode
    (fun a => decide (a.1.1.subgraph.graph.G.left a.2 ∈ a.1.1.U)) :=
  ((arcLeft.both (arcState.then reachBits)).then (getD boolCode false)).congr
    (fun a => getD_ofFn _ (a.1.1.subgraph.graph.G.left a.2) false)
def rightReached : Realizes arcCode boolCode
    (fun a => decide (a.1.1.subgraph.graph.G.right a.2 ∈ a.1.1.U)) :=
  ((arcRight.both (arcState.then reachBits)).then (getD boolCode false)).congr
    (fun a => getD_ofFn _ (a.1.1.subgraph.graph.G.right a.2) false)
instance poly_leftReached : PolyTime leftReached := by unfold leftReached; apply poly_congr
instance poly_rightReached : PolyTime rightReached := by unfold rightReached; apply poly_congr

def incident : Realizes arcCode boolCode (fun a => decide
    (a.2 ∈ a.1.1.subgraph.A ∧
      ((a.1.1.subgraph.graph.G.left a.2=a.1.2 ∧ a.1.1.subgraph.graph.G.right a.2 ∈ a.1.1.U) ∨
       (a.1.1.subgraph.graph.G.right a.2=a.1.2 ∧ a.1.1.subgraph.graph.G.left a.2 ∈ a.1.1.U)))) :=
  (arcSubedge.then selected).and
    (((arcLeft.finEq (arcVertex.then vertexIndex)).and rightReached).or
      ((arcRight.finEq (arcVertex.then vertexIndex)).and leftReached))
instance poly_incident : PolyTime incident := by unfold incident;infer_instance

def expands : Realizes vertexCode boolCode
    (fun v => decide (v.2 ∈ expand v.1.subgraph.graph.G v.1.subgraph.A v.1.U)) :=
  (reached.or (incident.existsFin (P:=fun a e => e ∈ a.1.subgraph.A ∧
    ((a.1.subgraph.graph.G.left e=a.2 ∧ a.1.subgraph.graph.G.right e ∈ a.1.U) ∨
     (a.1.subgraph.graph.G.right e=a.2 ∧ a.1.subgraph.graph.G.left e ∈ a.1.U)))
    (vertexContext.then reachM))).congr (by
    intro v
    congr 1
    apply propext
    simp only [expand,mem_union,mem_image,mem_filter]
    constructor
    · rintro (h|⟨e,he,h|h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨e,⟨he,h.2⟩,h.1⟩)
      · exact Or.inr ⟨e,⟨he,h.2⟩,h.1⟩
    · rintro ((h|⟨e,⟨he,hu⟩,hv⟩)|⟨e,⟨he,hu⟩,hv⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e,he,Or.inl ⟨hv,hu⟩⟩
      · exact Or.inr ⟨e,he,Or.inr ⟨hv,hu⟩⟩)
instance poly_expands : PolyTime expands := by unfold expands; apply poly_congr

def ReachState.next (s : ReachState) : ReachState :=
  ⟨s.subgraph,expand s.subgraph.graph.G s.subgraph.A s.U⟩
def next : Realizes reachCode reachCode ReachState.next :=
  (reachSubgraph.both (expands.tabulateFin reachN)).changeOutput reachCode ReachState.next (fun _ => rfl)
instance poly_next : PolyTime next := by unfold next; apply poly_changeOutput

lemma next_length (s : ReachState) : (reachCode s.next).length=(reachCode s).length := by
  simp only [reachCode,prodCode_length,ReachState.bits,bools_ofFn_length]
  rfl
instance size_next : IterateSize next := by
  refine ⟨⟨X,?_⟩⟩
  intro s k
  have he : (reachCode (ReachState.next^[k] s)).length=(reachCode s).length := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',next_length,ih]
  change (reachCode (ReachState.next^[k] s)).length ≤ (reachCode s).length+k
  rw [he];omega

abbrev InitVertex := Σ s : Subgraph, Fin s.graph.n
abbrev initVertexCode := finFamilyCode subgraphCode (fun s : Subgraph => s.graph.n)
def initBit : Realizes initVertexCode boolCode (fun p => decide (p.2.val=0)) :=
  (familyIndex.neq (constant initVertexCode natCode 0))
instance poly_initBit : PolyTime initBit := by unfold initBit;infer_instance

def Subgraph.start (s : Subgraph) : ReachState := ⟨s,univ.filter (fun v => v.val=0)⟩
def start : Realizes subgraphCode reachCode Subgraph.start :=
  ((identity subgraphCode).both (initBit.tabulateFin subgraphN)).changeOutput reachCode Subgraph.start (by
    intro s
    change prodCode subgraphCode boolsCode (s,List.ofFn (fun v : Fin s.graph.n => decide (v.val=0)))=_
    simp +instances only [reachCode,Subgraph.start,ReachState.bits,mem_filter,mem_univ,true_and])
instance poly_start : PolyTime start := by unfold start; apply poly_changeOutput

def Walk (s : Subgraph) : ReachState := ReachState.next^[s.graph.n] s.start
def walk : Realizes subgraphCode reachCode Walk := (subgraphN.both start).then next.iterate
instance poly_walk : PolyTime walk := by unfold walk; apply poly_then

def reachedAll : Realizes reachCode boolCode (fun s => decide (s.U=univ)) :=
  (reached.forallFin (P:=fun s v => v ∈ s.U) reachN).congr (by intro s;simp only [Finset.eq_univ_iff_forall])
instance poly_reachedAll : PolyTime reachedAll := by unfold reachedAll; apply poly_congr

lemma walk_eq (s : Subgraph) : Walk s =
    ⟨s,(expand s.graph.G s.A)^[s.graph.n] (univ.filter (fun v => v.val=0))⟩ := by
  have he (k : ℕ) : ReachState.next^[k] s.start =
      ⟨s,(expand s.graph.G s.A)^[k] (univ.filter (fun v => v.val=0))⟩ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply'];rfl
  exact he _

lemma walk_connected (s : Subgraph) : ((Walk s).U=univ) ↔ s.graph.G.Connected s.A := by
  rw [walk_eq]
  dsimp only
  by_cases hn : 0 < s.graph.n
  · let root : Fin s.graph.n := ⟨0,hn⟩
    have he : (univ.filter (fun v : Fin s.graph.n => v.val=0))={root} := by
      ext v;simp [Fin.ext_iff,root]
    rw [he]
    exact (connected_iff_reach s.graph.G s.A root).symm
  · have hn0 : s.graph.n=0 := by omega
    constructor
    · intro _ S hS hS'
      obtain ⟨v,_⟩ := hS
      exact (Nat.not_lt_zero v.val (hn0 ▸ v.isLt)).elim
    · intro _
      apply eq_univ_iff_forall.mpr
      intro v
      exact (Nat.not_lt_zero v.val (hn0 ▸ v.isLt)).elim

def connectedProgram : Realizes subgraphCode boolCode (fun s => connected s.graph.G s.A) :=
  (walk.then reachedAll).congr (by
    intro s
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq,connected_correct] using walk_connected s)
instance poly_connectedProgram : PolyTime connectedProgram := by unfold connectedProgram;infer_instance

abbrev EraseInput := Subgraph × ℕ
abbrev eraseInputCode := prodCode subgraphCode natCode
abbrev eraseContext := first subgraphCode natCode
abbrev eraseIndex := second subgraphCode natCode
abbrev EraseEdge := Σ p : EraseInput, Fin p.1.graph.m
abbrev eraseEdgeCode := finFamilyCode eraseInputCode (fun p : EraseInput => p.1.graph.m)
abbrev eraseEdgeContext : Realizes eraseEdgeCode eraseInputCode (fun p : EraseEdge => p.1) := familyFirst
abbrev eraseEdgeIndex : Realizes eraseEdgeCode natCode (fun p : EraseEdge => p.2.val) := familyIndex

def eraseSubedge : Realizes eraseEdgeCode sedgeCode (fun p => ⟨p.1.1,p.2⟩) :=
  ((eraseEdgeContext.then eraseContext).both eraseEdgeIndex).changeOutput sedgeCode
    (fun p => ⟨p.1.1,p.2⟩) (fun _ => rfl)
instance poly_eraseSubedge : PolyTime eraseSubedge := by unfold eraseSubedge; apply poly_changeOutput

def eraseBit : Realizes eraseEdgeCode boolCode
    (fun p => decide (p.2 ∈ p.1.1.A ∧ p.2.val ≠ p.1.2)) :=
  (eraseSubedge.then selected).and ((eraseEdgeIndex.neq (eraseEdgeContext.then eraseIndex)).not)
instance poly_eraseBit : PolyTime eraseBit := by unfold eraseBit;infer_instance

def erase (p : EraseInput) : Subgraph := ⟨p.1.graph,p.1.A.filter (fun e => e.val ≠ p.2)⟩
def eraseProgram : Realizes eraseInputCode subgraphCode erase :=
  ((eraseContext.then subgraphGraph).both
    (eraseBit.tabulateFin (eraseContext.then subgraphM))).changeOutput subgraphCode erase (by
      intro p
      simp +instances only [subgraphCode,Subgraph.bits,erase,mem_filter])
instance poly_eraseProgram : PolyTime eraseProgram := by unfold eraseProgram;infer_instance

def deleteAt (p : EraseInput) : Subgraph :=
  if connected (erase p).graph.G (erase p).A then erase p else p.1

def deleteProgram : Realizes eraseInputCode subgraphCode deleteAt :=
  (eraseProgram.then connectedProgram).ite eraseProgram eraseContext
instance poly_deleteProgram : PolyTime deleteProgram := by unfold deleteProgram; apply poly_ite

lemma deleteAt_graph (s : Subgraph) (i : ℕ) : (deleteAt (s,i)).graph=s.graph := by
  unfold deleteAt;split_ifs <;> rfl
lemma folded_graph (s : Subgraph) (xs : List ℕ) :
    (xs.foldl (fun s i => deleteAt (s,i)) s).graph=s.graph := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => rw [List.foldl_cons,ih,deleteAt_graph]

instance size_deleteProgram : FoldSize deleteProgram := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs he
  change (subgraphCode (ys.foldl (fun s i => deleteAt (s,i)) s)).length≤_
  rw [subgraph_length,folded_graph,←subgraph_length]
  change (subgraphCode s).length ≤ (prodCode subgraphCode (listCode natCode) (s,xs)).length
  exact le_prodCode_left (ea:=subgraphCode) (eb:=listCode natCode) (s,xs)

def whole : Realizes graphCode subgraphCode (fun g => ⟨g,univ⟩) :=
  ((identity graphCode).both
    (((constant graphCode boolCode true).both numEdges).then (replicateList boolCode))).changeOutput
      subgraphCode (fun g => ⟨g,univ⟩) (by intro g;simp [subgraphCode,Subgraph.bits,List.ofFn_const])
instance poly_whole : PolyTime whole := by unfold whole;infer_instance

lemma deleteAt_fin (g : Graph) (A : Finset (Fin g.m)) (e : Fin g.m) :
    deleteAt (⟨g,A⟩,e.val)=⟨g,eraseIf g.G A e⟩ := by
  have he : erase (⟨g,A⟩,e.val)=⟨g,A.erase e⟩ := by
    change (Subgraph.mk g (A.filter (fun i => i.val ≠ e.val)))=Subgraph.mk g (A.erase e)
    congr 1
    ext i
    simp [mem_erase,Fin.ext_iff,and_comm]
  unfold deleteAt
  rw [he]
  change (if connected g.G (A.erase e) then Subgraph.mk g (A.erase e) else Subgraph.mk g A)=_
  unfold eraseIf
  split_ifs <;> rfl

lemma fold_deletes (g : Graph) (A : Finset (Fin g.m)) (es : List (Fin g.m)) :
    (es.map Fin.val).foldl (fun s i => deleteAt (s,i)) ⟨g,A⟩=⟨g,deletePass g.G A es⟩ := by
  induction es generalizing A with
  | nil => rfl
  | cons e es ih =>
    rw [List.map_cons,List.foldl_cons,deleteAt_fin,ih]
    rfl

def treeProgram : Realizes graphCode boolsCode (fun g => List.ofFn (fun e => decide (e ∈ tree g.G))) :=
  ((((whole.both (numEdges.then range)).then deleteProgram.fold).then subgraphBits)).congr (by
    intro g
    have he : List.range g.m=(List.finRange g.m).map Fin.val := by simp
    change Subgraph.bits ((List.range g.m).foldl (fun s i => deleteAt (s,i)) ⟨g,univ⟩)=_
    rw [he,fold_deletes]
    rfl)
instance poly_treeProgram : PolyTime treeProgram := by unfold treeProgram; apply poly_congr

end AlgorithmicThinTrees.GreedyTree.Stack
end

end OAI
