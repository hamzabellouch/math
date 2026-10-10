import OAI.MeasureTheory.Falconer.Estimates.CellwisePairDeletion
import OAI.MeasureTheory.Falconer.Estimates.TroublesomePair

namespace OAI

/-! # Recombining relative pair refinements with the original source-class weights -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem relative_classwise_radial_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (I : Finset ι) (S : ι → Set (Space d)) (G : ι → Set (Space d × Space d))
    (hS : ∀ i ∈ I, MeasurableSet (S i)) (hG : ∀ i ∈ I, MeasurableSet (G i))
    (hpos : ∀ i ∈ I, μ (S i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint S)
    (t C : ℝ≥0∞) (r : ℝ)
    (hcost : ∀ i ∈ I, (ν.prod (ProbabilityTheory.cond μ (S i))) (G₀ \ G i) ≤ t)
    (hcap : ∀ i ∈ I, ∀ x u : Space d,
      ProbabilityTheory.cond μ (S i) {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G₀ ∧
      (ν.prod μ) (G₀ \ H) ≤ μ (⋃ i ∈ I, S i)ᶜ+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let U := ⋃ i ∈ I, G i ∩ (univ ×ˢ S i)
  let H := G₀ ∩ U
  have hH : MeasurableSet H := hG₀.inter (Finset.measurableSet_biUnion I
    (fun i hi => (hG i hi).inter (MeasurableSet.univ.prod (hS i hi))))
  have hmass : (∑ i ∈ I, μ (S i)) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hS]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ)
  have hreconstruct (i : ι) (hi : i ∈ I) (E : Set (Space d × Space d)) :
      μ (S i)*((ν.prod (ProbabilityTheory.cond μ (S i))) E) =
        (ν.prod (μ.restrict (S i))) E := by
    rw [ProbabilityTheory.cond,Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel (hpos i hi) (measure_ne_top μ _),one_mul]
  refine ⟨H,hH,inter_subset_left,?_,?_⟩
  · have hsub : G₀ \ H ⊆ (univ ×ˢ (⋃ i ∈ I, S i)ᶜ) ∪
        ⋃ i ∈ I, (G₀ \ G i) ∩ (univ ×ˢ S i) := by
      intro p hp
      by_cases hs : p.2 ∈ ⋃ i ∈ I, S i
      · obtain ⟨i,hi,hsi⟩ := mem_iUnion₂.mp hs
        right
        refine mem_iUnion₂.mpr ⟨i,hi,⟨hp.1,?_⟩,mem_univ _,hsi⟩
        intro hgi
        exact hp.2 ⟨hp.1,mem_iUnion₂.mpr ⟨i,hi,hgi,mem_univ _,hsi⟩⟩
      · exact Or.inl ⟨mem_univ _,hs⟩
    calc
      _ ≤ (ν.prod μ) (univ ×ˢ (⋃ i ∈ I, S i)ᶜ)+
          (ν.prod μ) (⋃ i ∈ I, (G₀ \ G i) ∩ (univ ×ˢ S i)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+
          ∑ i ∈ I, (ν.prod μ) ((G₀ \ G i) ∩ (univ ×ˢ S i)) := by
        simp only [Measure.prod_prod,measure_univ,one_mul]
        exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+∑ i ∈ I, μ (S i)*t := by
        apply add_le_add le_rfl (Finset.sum_le_sum ?_)
        intro i hi
        rw [← Measure.restrict_apply (hG₀.diff (hG i hi)),← Measure.prod_restrict,
          Measure.restrict_univ,← hreconstruct i hi]
        exact mul_le_mul' le_rfl (hcost i hi)
      _ = μ (⋃ i ∈ I, S i)ᶜ+(∑ i ∈ I, μ (S i))*t := by rw [Finset.sum_mul]
      _ ≤ _ := add_le_add le_rfl ((mul_le_mul' hmass le_rfl).trans_eq (one_mul t))
  · intro x u
    let A := fun i => {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r}
    have hsub : {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ⊆ ⋃ i ∈ I, S i ∩ A i := by
      intro z hz
      obtain ⟨i,hi,hgi,hsi⟩ := mem_iUnion₂.mp hz.1.2
      exact mem_iUnion₂.mpr ⟨i,hi,hsi.2,hgi,hz.2⟩
    calc
      _ ≤ ∑ i ∈ I, μ (S i ∩ A i) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ = ∑ i ∈ I, μ (S i)*ProbabilityTheory.cond μ (S i) (A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← ProbabilityTheory.cond_mul_eq_inter (hS i hi) (A i) μ,mul_comm]
      _ ≤ ∑ i ∈ I, μ (S i)*C := Finset.sum_le_sum (fun i hi =>
        mul_le_mul' le_rfl (hcap i hi x u))
      _ = (∑ i ∈ I, μ (S i))*C := (Finset.sum_mul _ _ _).symm
      _ ≤ C := (mul_le_mul' hmass le_rfl).trans_eq (one_mul C)

end Falconer

end OAI
