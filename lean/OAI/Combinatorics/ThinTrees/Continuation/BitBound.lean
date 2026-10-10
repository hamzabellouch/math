import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Realization

namespace OAI

/-! Continuation bit bound. -/

section

namespace CurrentKS.Realization
open CleanRoutine
lemma QParts.neg {b : ℕ} {q : ℚ} (h : QParts b q) : QParts b (-q) := by
  simpa only [QParts,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using h
lemma QParts.sub {b c : ℕ} {q v : ℚ} (h : QParts b q) (hv : QParts c v) :
    QParts (b+c+1) (q-v) := by simpa only [sub_eq_add_neg] using h.add hv.neg
lemma QParts.max {b : ℕ} {q v : ℚ} (h : QParts b q) (hv : QParts b v) :
    QParts b (max q v) := by
  rcases le_total q v with hl|hl
  · simpa only [max_eq_right hl] using hv
  · simpa only [max_eq_left hl] using h
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

structure MeshPoint where
  graph : Graph
  v : Fin (dimension graph.n graph.m) → ℚ

def meshPointCode (a : MeshPoint) : Word := prodCode graphCode vectorCode (a.graph,List.ofFn a.v)
abbrev meshView : Realizes meshPointCode (prodCode graphCode vectorCode)
    (fun a => (a.graph,List.ofFn a.v)) :=
  (identity (prodCode graphCode vectorCode)).reindex meshPointCode
    (fun a => (a.graph,List.ofFn a.v)) (fun _ => rfl)
private instance poly_meshView : PolyTime meshView := by
  unfold meshView
  apply poly_reindex

abbrev meshGraph := meshView.then (first graphCode vectorCode)
abbrev meshVector := meshView.then (second graphCode vectorCode)
def meshRaw : Realizes meshPointCode matrixObjectCode (fun a => ⟨a.graph.n,rawMatrix a.v⟩) :=
  ((meshGraph.then numVertices).both
    ((((meshGraph.then numVertices).both (meshGraph.then numEdges)).both meshVector).then raw)).changeOutput
      matrixObjectCode (fun a => ⟨a.graph.n,rawMatrix a.v⟩) (by
        intro a
        change prodCode natCode matrixCode (a.graph.n,
          (List.range a.graph.n).map (fun i => (List.range a.graph.n).map
            (fun j => (List.ofFn a.v).getD (j+a.graph.n*i) 0)))=_
        rw [raw_data];rfl)
instance poly_meshRaw : PolyTime meshRaw := by
  have hg : PolyTime meshGraph := by unfold meshGraph; apply poly_then
  have hv : PolyTime meshVector := by unfold meshVector; apply poly_then
  unfold meshRaw
  apply poly_changeOutput

lemma response_parts_bound : ∃b : NaturalPolynomial,∀p : Params,∀i j,
    QParts (b.eval (graphCode p.graph).length)
      (qresponse (rawMatrix (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0)) i j) := by
  let a := fun p : Params => MeshPoint.mk p.graph
    (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0)
  have hin := isPoly_pair (isPoly_self (fun p : Params => (graphCode p.graph).length)) search_output_bound
  have hout := (RunsPoly.of_poly (meshRaw.then GraphStack.response) a hin).output
  obtain ⟨b,hb⟩ := hout
  refine ⟨b,?_⟩
  intro p i j
  have hh := matrixParts_length (matrixData (qresponse (rawMatrix (a p).v)))
  exact (hh _ (List.mem_ofFn.mpr ⟨i,rfl⟩) _ (List.mem_ofFn.mpr ⟨j,rfl⟩)).mono (hb p)

abbrev coefficients :=
  let t := extractionGraph.then graphStep
  ((constant extractionInputCode ratCode 1).add t).cons
    (((constant extractionInputCode ratCode 1).sub t).cons
      (((((constant extractionInputCode ratCode 2).mul (extractionCount.then gainProgram)).mul
        (extractionCount.then natToRat)).mul t).cons
          (t.cons ((extractionGraph.then graphBaseline).then (singleton ratCode)))))

lemma coefficients_parts_bound : ∃b : NaturalPolynomial,∀G r,
    let B := b.eval (extractionInputCode (G,r)).length
    QParts B (1+stepQ G.m) ∧ QParts B (1-stepQ G.m) ∧
      QParts B (2*gain r*r*stepQ G.m) ∧ QParts B (stepQ G.m) ∧ QParts B (baselineQ G.m) := by
  obtain ⟨b,hb⟩ := (RunsPoly.of_poly coefficients id
    (isPoly_self (fun p => (extractionInputCode p).length))).output
  refine ⟨b,?_⟩
  intro G r
  have hh : ∀q∈[1+stepQ G.m,1-stepQ G.m,2*gain r*r*stepQ G.m,stepQ G.m,baselineQ G.m],
      QParts (b.eval (extractionInputCode (G,r)).length) q := by
    intro q hq
    exact (qparts_length q).mono ((mem_length_le_code _ hq).trans (hb (G,r)))
  exact ⟨hh _ (by simp),hh _ (by simp),hh _ (by simp),hh _ (by simp),hh _ (by simp)⟩

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization
open CurrentKS.CleanRoutine KS.W23
open Stack GraphStack

variable {n m : ℕ}
def State.Parts (b : ℕ) (a : State n m) : Prop :=
  QParts b a.scale ∧ QParts b a.quality ∧ (∀i j,QParts b (a.matrix i j)) ∧
    ∀e,QParts b (a.capacity e)
lemma State.Parts.mono {b c : ℕ} {a : State n m} (ha : a.Parts b) (h : b≤c) : a.Parts c :=
  ⟨ha.1.mono h,ha.2.1.mono h,fun i j => (ha.2.2.1 i j).mono h,fun e => (ha.2.2.2 e).mono h⟩

lemma update_parts_bound : ∃P : NaturalPolynomial,∀G : Graph,∀r a b,
    a.Parts b → (update G.G r (gain r) a).Parts
      (b+P.eval (extractionInputCode (G,r)).length) := by
  obtain ⟨c,hc⟩ := coefficients_parts_bound
  obtain ⟨v,hv⟩ := search_parts_bound
  obtain ⟨w,hw⟩ := response_parts_bound
  refine ⟨3*c+v+w+2,?_⟩
  intro G r a b ha
  let p : Params := ⟨G,a.scale,baselineQ G.m,stepQ G.m,
    target G.m r a.quality (gain r),errorQ G.n G.m,a.capacity⟩
  let L := (extractionInputCode (G,r)).length
  let C := c.eval L
  let V := v.eval L
  let W := w.eval L
  have hGl : (graphCode G).length≤L := le_prodCode_left (G,r)
  obtain ⟨hplus,hminus,hloss,ht,hbase⟩ := hc G r
  have hvec : ∀i,QParts V (search G.G a.scale (target G.m r a.quality (gain r)) a.capacity i) :=
    fun i => (hv p i).mono (v.eval_mono hGl)
  have hresp : ∀i j,QParts W (qresponse (rawMatrix (search G.G a.scale
      (target G.m r a.quality (gain r)) a.capacity)) i j) :=
    fun i j => (hw p i j).mono (w.eval_mono hGl)
  change (update G.G r (gain r) a).Parts (b+(3*C+V+W+2))
  refine ⟨(hplus.mul ha.1).mono (by dsimp [C,V,W,L];omega),(ha.2.1.sub hloss).mono (by dsimp [C,V,W,L];omega),?_,?_⟩
  · intro i j
    exact ((hminus.mul (ha.2.2.1 i j)).add (ht.mul (hresp i j))).mono (by dsimp [C,V,W,L];omega)
  · intro e
    change QParts _ (if 0<a.capacity e then max 0 (_-baselineQ G.m) else 0)
    split
    · exact ((qparts_zero (V+C+1)).max ((hvec (edgeIndex 1 e)).sub hbase)).mono (by dsimp [C,V,W,L];omega)
    · exact qparts_zero _

lemma advance_parts {P : NaturalPolynomial}
    (hP : ∀G : Graph,∀r a b, a.Parts b → (update G.G r (gain r) a).Parts
      (b+P.eval (extractionInputCode (G,r)).length))
    (G : Graph) (r : ℕ) {a : State G.n G.m} {b : ℕ} (ha : a.Parts b) :
    ∀k, ((advance G.G r)^[k] a).Parts (b+k*P.eval (extractionInputCode (G,r)).length) := by
  intro k
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [advance]
    split
    · simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hP G r _ _ ih
    · exact ih.mono (by simp only [Nat.add_mul,Nat.one_mul];omega)

end AlgorithmicThinTrees.MetricTests.RationalStep

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

lemma loop_parts (a : Loop) : a.state.Parts (loopCode a).length := by
  let L := (loopCode a).length
  have ht : (loopTailCode a.data.2.2).length≤L :=
    (le_prodCode_right a.data.2).trans (le_prodCode_right a.data)
  have hq := (le_prodCode_right a.data.2.2).trans ht
  have harr := (le_prodCode_right a.data.2.2.2).trans hq
  have hs := (le_prodCode_left a.data.2.2).trans ht
  have hQ := (le_prodCode_left a.data.2.2.2).trans hq
  have hmat := (le_prodCode_left a.data.2.2.2.2).trans harr
  have hcap := (le_prodCode_right a.data.2.2.2.2).trans harr
  refine ⟨(qparts_length _).mono hs,(qparts_length _).mono hQ,?_,?_⟩
  · intro i j
    exact ((matrixParts_length (matrixData a.state.matrix)) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
      _ (List.mem_ofFn.mpr ⟨j,rfl⟩)).mono hmat
  · intro e
    exact (qparts_length _).mono ((mem_length_le_code (List.ofFn a.state.capacity)
      (List.mem_ofFn.mpr ⟨e,rfl⟩)).trans hcap)

lemma loop_parts_length (a : Loop) {b : ℕ} (hb : a.state.Parts b) :
    (loopCode a).length ≤ 2*(graphCode a.graph).length+1+2*a.count+1+
      (4*(4*b+7)+3+2*(a.graph.n*(2*(a.graph.n*(2*(4*b+7)+1))+1))+
        a.graph.m*(2*(4*b+7)+1)) := by
  have hmat := matrixCode_parts_bound a.state.matrix hb.2.2.1
  have hvec := listCode_length_bound (List.ofFn a.state.capacity) (4*b+7)
    (by intro q hq;obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq;exact (hb.2.2.2 e).length)
  rw [List.length_ofFn] at hvec
  change (vectorCode (List.ofFn a.state.capacity)).length ≤ _ at hvec
  have hs := hb.1.length
  have hq := hb.2.1.length
  simp only [loopCode,loopDataCode,Loop.data,loopTailCode,prodCode_length,natCode,List.length_replicate]
  omega

instance size_next : IterateSize next := by
  obtain ⟨P,hP⟩ := update_parts_bound
  let L := fun u : Loop×ℕ => (loopCode u.1).length+u.2
  have ha : IsPoly L (fun u => (loopCode u.1).length) := (isPoly_self L).mono (fun u => Nat.le_add_right _ _)
  have hk : IsPoly L Prod.snd := (isPoly_self L).mono (fun u => Nat.le_add_left _ _)
  have hg := (RunsPoly.of_poly loopGraph Prod.fst ha).output
  have hr := (RunsPoly.of_poly loopCount Prod.fst ha).output
  have hr' : IsPoly L (fun u => u.1.count) := by simpa only [natCode,List.length_replicate] using hr
  have hpar := isPoly_pair hg hr
  have hn := ((RunsPoly.of_poly numVertices (fun u : Loop×ℕ => u.1.graph) hg).output)
  have hm := ((RunsPoly.of_poly numEdges (fun u : Loop×ℕ => u.1.graph) hg).output)
  have hn' : IsPoly L (fun u => u.1.graph.n) := by simpa only [natCode,List.length_replicate,Graph.data] using hn
  have hm' : IsPoly L (fun u => u.1.graph.m) := by simpa only [natCode,List.length_replicate,Graph.data] using hm
  have hb := ha.add (hk.mul (hpar.eval P))
  have hrat := ((isPoly_const L 4).mul hb).add (isPoly_const L 7)
  have helem := ((isPoly_const L 2).mul hrat).add (isPoly_const L 1)
  have hmat := hn'.mul (((isPoly_const L 2).mul (hn'.mul helem)).add (isPoly_const L 1))
  have hvec := hm'.mul helem
  have htotal := (((((isPoly_const L 2).mul hg).add (isPoly_const L 1)).add
    ((isPoly_const L 2).mul hr')).add (isPoly_const L 1)).add
      (((((isPoly_const L 4).mul hrat).add (isPoly_const L 3)).add
        ((isPoly_const L 2).mul hmat)).add hvec)
  obtain ⟨Q,hQ⟩ := htotal
  refine ⟨⟨Q,?_⟩⟩
  intro a k
  rw [next_iterate]
  apply (loop_parts_length ⟨a.graph,a.count,(advance a.graph.G a.count)^[k] a.state⟩
    (advance_parts hP a.graph a.count (loop_parts a) k)).trans
  exact hQ (a,k)

instance poly_extract : PolyTime extract := by unfold extract; apply poly_congr

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
