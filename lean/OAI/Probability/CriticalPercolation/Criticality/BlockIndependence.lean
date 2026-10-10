import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma blockSigma_mono {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)

lemma independent_disjoint_blocks (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint coordinateSigma_le (independent_coordinates q) h

theorem independent_block_family (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndep (fun i => blockSigma (S i)) (law q) := by
  apply (iIndep_iff _ _).mpr
  intro t
  induction t using Finset.induction_on with
  | empty => intro f hf; simp
  | @insert i t hi ih =>
    intro f hf
    let T := ⋃ j ∈ t, S j
    have hj : ∀ j ∈ t, blockSigma (S j) ≤ blockSigma T := by
      intro j hj
      exact blockSigma_mono (fun e he => Set.mem_iUnion₂.mpr ⟨j,hj,he⟩)
    have hm : MeasurableSet[blockSigma T] (⋂ j ∈ t, f j) := by
      apply MeasurableSet.biInter t.finite_toSet.countable
      intro j hjt
      exact hj j hjt _ (hf j (Finset.mem_insert_of_mem hjt))
    have hdis : Disjoint (S i) T := by
      apply Set.disjoint_left.mpr
      intro e hei heT
      obtain ⟨j,hjt,hje⟩ := Set.mem_iUnion₂.mp heT
      exact Set.disjoint_left.mp (hS (by intro h; subst j; exact hi hjt)) hei hje
    have hmuli := ((independent_disjoint_blocks q (S i) T hdis).indepSet_of_measurableSet
      (hf i (Finset.mem_insert_self i t)) hm).measure_inter_eq_mul
    rw [Finset.set_biInter_insert,Finset.prod_insert hi,hmuli]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma independent_block_events (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (A : I → Set (Set E))
    (hA : ∀ i, MeasurableSet[blockSigma (S i)] (A i)) : iIndepSet A (law q) :=
  (independent_block_family q S hS).iIndepSets'.iIndepSet_of_mem hA
    (fun i => blockSigma_le (S i) _ (hA i))

def closedBlock (S : Set E) : Set (Set E) := {ω | Disjoint S ω}

lemma measurableSet_closed_coordinate (e : E) :
    MeasurableSet[coordinateSigma e] {ω : Set E | e ∉ ω} := by
  refine ⟨{False},MeasurableSet.singleton _,?_⟩
  ext ω
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  constructor
  · intro h hp
    exact Eq.mp h hp
  · intro h
    exact propext (iff_false_intro h)

lemma measurableSet_closedBlock (S : Set E) (hS : S.Countable) :
    MeasurableSet[blockSigma S] (closedBlock S) := by
  have heq : closedBlock S = ⋂ e ∈ S, {ω : Set E | e ∉ ω} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left]
  rw [heq]
  apply MeasurableSet.biInter hS
  intro e he
  exact (le_iSup_of_le e (le_iSup_of_le he le_rfl) : coordinateSigma e ≤ blockSigma S)
    _ (measurableSet_closed_coordinate e)

lemma law_closedBlock (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
    law q (closedBlock S) = ∏ e ∈ hS.toFinset, bitMeasure (q e) {False} := by
  have heq : closedBlock S = ⋂ e ∈ hS.toFinset, {ω : Set E | (e ∈ ω) = False} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left,
      Set.Finite.mem_toFinset]
    constructor
    · intro h e he
      exact propext (iff_false_intro (h he))
    · intro h e he hp
      exact Eq.mp (h e he) hp
  rw [heq,(independent_coordinates q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e False)
  · intro e _
    exact ⟨{False},MeasurableSet.singleton _,rfl⟩

lemma law_closedBlock_const (p : unitInterval) (S : Set E) (hS : S.Finite) :
    law (fun _ : E => p) (closedBlock S) =
      (bitMeasure p {False}) ^ S.ncard := by
  rw [law_closedBlock (fun _ : E => p) S hS,Finset.prod_const]
  rw [Set.ncard_eq_toFinset_card S hS]

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
