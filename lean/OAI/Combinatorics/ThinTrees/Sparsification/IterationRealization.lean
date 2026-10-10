import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.GreedyRealization
import OAI.Combinatorics.ThinTrees.Encoding.SelectionRealization
import OAI.Combinatorics.ThinTrees.Sparsification.RationalIteration

namespace OAI

/-! Iteration realization. -/

section

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep MetricTests.RationalStep.Stack OrderedGraph

lemma nextCount_le (r : ℕ) : nextCount r ≤ r := by
  unfold nextCount
  apply (Nat.floor_mono (show (1-16*countError r)*(r:ℚ)/2 ≤ (r:ℚ) from ?_)).trans_eq
    (Nat.floor_natCast r)
  have : 0 ≤ countError r := by unfold countError; positivity
  have : 0 ≤ countError r*(r:ℚ) := mul_nonneg this (Nat.cast_nonneg _)
  nlinarith

def nextCountBinary : Realizes natCode binaryNatCode nextCount :=
  ((((constant natCode ratCode 1).sub ((constant natCode ratCode 16).mul
    ((constant natCode ratCode 1).div ((unaryRoot 16 (by decide)).then natToRat)))).mul natToRat).div
      (constant natCode ratCode 2)).then ratNatFloorBinary
instance poly_nextCountBinary : PolyTime nextCountBinary := by
  unfold nextCountBinary
  apply poly_then

def nextCountProgram : Realizes natCode natCode nextCount := nextCountBinary.then binaryToNat
instance poly_nextCountProgram : PolyTime nextCountProgram := by
  apply PolyTime.mk
  have hb := RunsPoly.of_poly nextCountBinary id (isPoly_self (fun r => (natCode r).length))
  have hn : IsPoly (fun r => (natCode r).length) nextCount :=
    (isPoly_self (fun r => (natCode r).length)).mono (fun r => by
      simpa only [natCode,List.length_replicate] using nextCount_le r)
  exact (hb.then (runsPoly_binaryToNat _ hb.output hn)).cost

structure State where
  problem : Problem
  labels : Fin problem.m → ℕ

def stateCode (s : State) : Word := prodCode problemCode indicesCode
  (s.problem,List.ofFn s.labels)
abbrev stateView : Realizes stateCode (prodCode problemCode indicesCode)
    (fun s => (s.problem,List.ofFn s.labels)) :=
  (identity (prodCode problemCode indicesCode)).reindex stateCode
    (fun s => (s.problem,List.ofFn s.labels)) (fun _ => rfl)
private instance poly_stateView : PolyTime stateView := by
  unfold stateView
  apply poly_reindex

abbrev problem := stateView.then (first problemCode indicesCode)
private instance poly_problem : PolyTime problem := by
  unfold problem
  apply poly_then

abbrev labels := stateView.then (second problemCode indicesCode)
private instance poly_labels : PolyTime labels := by
  unfold labels
  apply poly_then

abbrev graph := problem.then problemGraph
private instance poly_graph : PolyTime graph := by
  unfold graph
  apply poly_then

abbrev count := problem.then problemCount
private instance poly_count : PolyTime count := by
  unfold count
  apply poly_then

def State.restrict (s : State) (A : Finset (Fin s.problem.m)) : State :=
  ⟨⟨s.problem.d,A.card,nextCount s.problem.r,OrderedGraph.restrict s.problem.G A⟩,
    fun e => s.labels (edgeEmbedding A e)⟩
def halve (s : State) : State := s.restrict (sparsify s.problem.G s.problem.r)
def step (R : ℕ) (s : State) : State := if R ≤ s.problem.r then halve s else s

def selectState : Realizes (prodCode stateCode boolsCode) stateCode
    (fun p => p.1.restrict (univ.filter (fun e => p.2.getD e.val false))) := by
  let a := first stateCode boolsCode
  let b := second stateCode boolsCode

  let entry : Realizes (prodCode (prodCode stateCode boolsCode) natCode) boolCode
      (fun q => q.1.2.getD q.2 false) :=
    ((second (prodCode stateCode boolsCode) natCode).both
      ((first (prodCode stateCode boolsCode) natCode).then b)).then (getD boolCode false)
  let bits := (((identity (prodCode stateCode boolsCode)).both
    (a.then graph |>.then numEdges)).then entry.tabulate)
  let ls := (bits.both (a.then graph |>.then lefts)).then (maskArray natCode 0)
  let rs := (bits.both (a.then graph |>.then rights)).then (maskArray natCode 0)
  let labs := (bits.both (a.then labels)).then (maskArray natCode 0)
  let gg := (a.then graph |>.then numVertices).both (ls.both rs)
  exact ((gg.both (a.then count |>.then nextCountProgram)).both labs).changeOutput stateCode
    (fun p => p.1.restrict (univ.filter (fun e => p.2.getD e.val false))) (by
      intro p
      let A := univ.filter (fun e : Fin p.1.problem.m => p.2.getD e.val false)
      have hb : (List.range p.1.problem.m).map (fun i => p.2.getD i false)=
          List.ofFn (fun e => decide (e ∈ A)) := by
        rw [range_map_fin]
        simp [A]
      change prodCode (prodCode graphDataCode natCode) indicesCode
        ((_,_),_) = _
      dsimp only [id,Problem.graph,Graph.data]
      rw [hb,maskArray_data,maskArray_data,maskArray_data]
      rfl)
instance poly_selectState : PolyTime selectState := by
  unfold selectState
  dsimp only
  refine @poly_changeOutput _ _ _ _ _ _ _ _ _ _ ?_
  refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_ <;> infer_instance

def halveProgram : Realizes stateCode stateCode halve :=
  (((identity stateCode).both (problem.then sparsifyProgram)).then selectState).congr (by
    intro s
    have he : univ.filter (fun e : Fin s.problem.m =>
        (List.ofFn (fun e => decide (e ∈ sparsify s.problem.G s.problem.r))).getD e.val false)=
        sparsify s.problem.G s.problem.r := by
      ext e
      simp
    change s.restrict _=s.restrict _
    exact congrArg (State.restrict s) he)

def large (R : ℕ) : Realizes stateCode boolCode (fun s => decide (R ≤ s.problem.r)) :=
  ((constant stateCode natCode R).both count).then natLE
instance poly_large (R : ℕ) : PolyTime (large R) := by unfold large;apply poly_then

def stepProgram (R : ℕ) : Realizes stateCode stateCode (step R) :=
  ((large R).ite halveProgram (identity stateCode)).congr (by intro s;simp [step])

def finishData (s : State) : List ℕ :=
  List.ofFn (fun e => s.labels (edgeEmbedding (GreedyTree.tree s.problem.G) e))
def finish : Realizes stateCode indicesCode finishData :=
  ((((graph.then GreedyTree.Stack.treeProgram).both labels).then (maskArray natCode 0))).congr
    (fun s => maskArray_data _ s.labels 0)
instance poly_finish : PolyTime finish := by unfold finish;apply poly_congr

lemma restrict_length (s : State) (A : Finset (Fin s.problem.m)) :
    (stateCode (s.restrict A)).length≤(stateCode s).length := by
  have hl := listCode_selected_le natCode A (fun e => (s.problem.G.left e).val)
  have hr := listCode_selected_le natCode A (fun e => (s.problem.G.right e).val)
  have hlabels := listCode_selected_le natCode A s.labels
  have hn := nextCount_le s.problem.r
  simp only [stateCode,State.restrict,problemCode,extractionInputCode,Problem.graph,graphCode,
    graphDataCode,Graph.data,prodCode_length,natCode,List.length_replicate,
    OrderedGraph.restrict,indicesCode] at *
  omega
lemma step_length (R : ℕ) (s : State) : (stateCode (step R s)).length≤(stateCode s).length := by
  unfold step
  split
  · exact restrict_length _ _
  · rfl
lemma orbit_length (R t : ℕ) (s : State) :
    (stateCode ((step R)^[t] s)).length≤(stateCode s).length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply'];exact (step_length _ _).trans ih

lemma orbit_packed {R : ℕ} (_hR : 4 ≤ R) (hb : RoundBound R) (s : State)
    (hn : 2 ≤ s.problem.d+1) (hp : s.problem.G.TreePackable univ s.problem.r)
    (t : ℕ) :
    2 ≤ ((step R)^[t] s).problem.d+1 ∧
      ((step R)^[t] s).problem.G.TreePackable univ ((step R)^[t] s).problem.r := by
  induction t with
  | zero => exact ⟨hn,hp⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hh : R ≤ ((step R)^[t] s).problem.r
    · rw [step,ite_eq_left hh]
      exact ⟨ih.1,OrderedGraph.restrict_packable _ _
        (hb _ hh _ _ _ ih.1 ih.2).2.2.2.1⟩
    · rw [step,ite_eq_right hh];exact ih

lemma runsPoly_step {R T : ℕ} (hTR : T ≤ R)
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,T ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
      RunsPoly L sparsifyProgram a)
    {ι : Type} {L : ι → ℕ} (a : ι → State)
    (ha : IsPoly L (fun i => (stateCode (a i)).length))
    (hp : ∀i,2 ≤ (a i).problem.d+1 ∧ (a i).problem.G.TreePackable univ (a i).problem.r) :
    RunsPoly L (stepProgram R) a := by
  unfold stepProgram
  apply RunsPoly.congr
  apply RunsPoly.ite_on (RunsPoly.of_poly _ a ha)
  have hh : IsPoly (fun i : {i // R ≤ (a i).problem.r} => L i.val)
      (fun i => halveProgram.cost (a i.val)) := by
    have hi := RunsPoly.of_poly problem (fun i : {i // R ≤ (a i).problem.r} => a i.val)
      (ha.reindex Subtype.val)
    have hs := htime (fun i : {i // R ≤ (a i).problem.r} => (a i.val).problem) hi.output
      (fun i => ⟨hTR.trans i.property,(hp i.val).1,(hp i.val).2⟩)
    have hh := (RunsPoly.of_poly (identity stateCode)
      (fun i : {i // R ≤ (a i).problem.r} => a i.val) (ha.reindex Subtype.val)).both
        (hi.then hs)
    have hz : RunsPoly (fun i : {i // R ≤ (a i).problem.r} => L i.val)
        halveProgram (fun i => a i.val) := by
      unfold halveProgram;apply RunsPoly.congr;exact hh.then_poly selectState
    exact hz.cost
  have hl := (RunsPoly.of_poly (identity stateCode)
    (fun i : {i // ¬R ≤ (a i).problem.r} => a i.val) (ha.reindex Subtype.val)).cost
  have hz := isPoly_dite (L:=L) (P:=fun i => R ≤ (a i).problem.r)
    (f:=fun i _ => halveProgram.cost (a i))
    (g:=fun i _ => (identity stateCode).cost (a i)) hh hl
  convert hz using 1
  funext i
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

def run (R : ℕ) : Realizes (prodCode natCode stateCode) indicesCode
    (fun p => finishData ((step R)^[p.1] p.2)) := (stepProgram R).iterate.then finish

lemma runsPoly_run {R T : ℕ} (hR : 4 ≤ R) (hb : RoundBound R) (hTR : T ≤ R)
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,T ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
      RunsPoly L sparsifyProgram a)
    {ι : Type} {L : ι → ℕ} (a : ι → ℕ×State)
    (ha : IsPoly L (fun i => (prodCode natCode stateCode (a i)).length))
    (hp : ∀i,2 ≤ (a i).2.problem.d+1 ∧
      (a i).2.problem.G.TreePackable univ (a i).2.problem.r) : RunsPoly L (run R) a := by
  have hi : IsPoly L (fun i => (stateCode (a i).2).length) :=
    ha.mono (fun i => le_prodCode_right (ea:=natCode) (eb:=stateCode) (a i))
  have hs := runsPoly_step hTR htime (fun p : ι×ℕ => (step R)^[p.2] (a p.1).2)
    ((hi.reindex Prod.fst).mono (fun p => orbit_length R p.2 (a p.1).2))
    (fun p => orbit_packed hR hb (a p.1).2 (hp p.1).1 (hp p.1).2 p.2)
  apply (runsPoly_iterate _ a ha ?_).then_poly finish
  obtain ⟨q,hq⟩ := hs.cost
  exact ⟨q,fun i j _ => hq (i,j)⟩

end AlgorithmicThinTrees.Iteration.Stack

namespace AlgorithmicThinTrees.OrderedGraph
open StrongThinTree Finset
lemma sorted_lift {m : ℕ} (A : Finset (Fin m)) (B : Finset (Fin A.card)) :
    List.ofFn (edgeEmbedding (liftEdges A B)) =
      List.ofFn (fun i => edgeEmbedding A (edgeEmbedding B i)) := by
  have ha := List.sortedLT_ofFn_iff.mpr ((liftEdges A B).orderEmbOfFin rfl).strictMono
  have hb := List.sortedLT_ofFn_iff.mpr
    ((A.orderEmbOfFin rfl).strictMono.comp (B.orderEmbOfFin rfl).strictMono)
  apply ha.eq_of_mem_iff hb
  · intro e
    simp only [List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨j,hj,hji⟩ := mem_map.mp (embedding_mem (liftEdges A B) i)
      obtain ⟨l,rfl⟩ := embedding_surj B hj
      exact ⟨l,hji⟩
    · rintro ⟨i,rfl⟩
      exact embedding_surj (liftEdges A B) (mem_map.mpr ⟨_,embedding_mem B i,rfl⟩)

lemma mapped_sorted_lift {m : ℕ} (A : Finset (Fin m)) (B : Finset (Fin A.card)) (f : Fin m → ℕ) :
    List.ofFn (fun i => f (edgeEmbedding (liftEdges A B) i)) =
      List.ofFn (fun i => f (edgeEmbedding A (edgeEmbedding B i))) := by
  have h := congrArg (List.map f) (sorted_lift A B)
  simpa only [List.map_ofFn,Function.comp_def] using h
end AlgorithmicThinTrees.OrderedGraph

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep OrderedGraph

lemma run_data (R fuel : ℕ) (s : State) :
    finishData ((step R)^[fuel] s)=
      List.ofFn (fun e => s.labels (edgeEmbedding
        (iterate R fuel s.problem.r s.problem.d s.problem.m s.problem.G) e)) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ t ih =>
    by_cases hh : R ≤ s.problem.r
    · rw [Function.iterate_succ_apply,step,ite_eq_left hh,ih,iterate,ite_eq_left hh]
      exact (mapped_sorted_lift (sparsify s.problem.G s.problem.r)
        (iterate R t (nextCount s.problem.r) s.problem.d _
          (OrderedGraph.restrict s.problem.G (sparsify s.problem.G s.problem.r))) s.labels).symm
    · have hfix : step R s=s := by rw [step,ite_eq_right hh]
      have horb : (step R)^[t+1] s=s := Function.iterate_fixed hfix _
      rw [horb,iterate,ite_eq_right hh]
      rfl

def initialCountProgram : Realizes natCode natCode initialCount :=
  let h := (identity natCode).ndiv (constant natCode natCode 2)
  (((constant natCode natCode 1).nlt h).ite h (constant natCode natCode 1)).congr (by
    intro k
    simp only [decide_eq_true_eq,initialCount,id_eq]
    split_ifs with hh
    · exact (max_eq_right (by omega)).symm
    · exact (max_eq_left (by omega)).symm)
instance poly_initialCountProgram : PolyTime initialCountProgram := by
  unfold initialCountProgram;infer_instance

abbrev TreeProblem := Problem

def start (p : TreeProblem) : ℕ×State :=
  (initialCount p.r,⟨⟨p.d,p.m,initialCount p.r,p.G⟩,fun e => e.val⟩)
def startProgram : Realizes problemCode (prodCode natCode stateCode) start :=
  let r := problemCount.then initialCountProgram
  let lab := problemM.then CurrentKS.Realization.range
  (r.both ((problemGraph.both r).both lab)).changeOutput
    (prodCode natCode stateCode) start (by
      intro p
      change prodCode natCode (prodCode (prodCode graphCode natCode) indicesCode)
        (_,(_,List.range p.m))=_
      have he : List.range p.m=List.ofFn (fun e : Fin p.m => e.val) := by
        simpa only [List.map_id, id_eq] using (range_map_fin (n:=p.m) (f:=id))
      rw [he]
      rfl)
instance poly_startProgram : PolyTime startProgram := by unfold startProgram;infer_instance

def treeData (R : ℕ) (p : TreeProblem) : List ℕ :=
  List.ofFn (fun e => (edgeEmbedding (Iteration.tree R p.r p.G) e).val)
def treeProgram (R : ℕ) : Realizes problemCode indicesCode (treeData R) :=
  (startProgram.then (run R)).congr (fun p => run_data R (initialCount p.r) (start p).2)

lemma runsPoly_tree {R T : ℕ} (hR : 4 ≤ R) (hb : RoundBound R) (hTR : T ≤ R)
    (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
      IsPoly L (fun i => (problemCode (a i)).length) →
      (∀i,T ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
      RunsPoly L sparsifyProgram a)
    {ι : Type} {L : ι → ℕ} (a : ι → Problem)
    (ha : IsPoly L (fun i => (problemCode (a i)).length))
    (hp : ∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) :
    RunsPoly L (treeProgram R) a := by
  have hs := RunsPoly.of_poly startProgram a ha
  unfold treeProgram
  apply RunsPoly.congr
  apply hs.then
  apply runsPoly_run hR hb hTR htime _ hs.output
  intro i
  exact ⟨(hp i).1,initial_packable _ (by omega) (hp i).2.1 (hp i).2.2⟩

end AlgorithmicThinTrees.Iteration.Stack
end

end OAI
