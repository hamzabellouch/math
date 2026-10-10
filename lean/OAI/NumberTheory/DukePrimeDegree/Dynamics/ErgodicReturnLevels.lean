import OAI.NumberTheory.DukePrimeDegree.Entropy.FirstReturnPartition

namespace OAI

/-! # Visiting arbitrarily high positive return levels

This is the ergodic case of the recurrent-section construction. The
ergodicity premise is explicit here and is not added to the packet theorem.
-/

noncomputable section
open MeasureTheory Set Filter
namespace DukePrimeDegree

lemma ae_future_visit_of_positive
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) {S : Set Y}
    (hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    ∀ᵐ x ∂μ, ∃ k : ℕ, T^[k] x ∈ S := by
  let U : Set Y := ⋃ k : ℕ, T^[k] ⁻¹' S
  have hU : MeasurableSet U :=
    MeasurableSet.iUnion fun k => hS.preimage (hT.measurable.iterate k)
  have hpre : T ⁻¹' U ⊆ U := by
    intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨k+1,?_⟩
    simpa only [mem_preimage,Function.iterate_succ_apply] using hk
  rcases hT.ae_empty_or_univ_of_preimage_ae_le hU.nullMeasurableSet
      (ae_of_all μ (fun _ hx => hpre hx)) with hnull | hfull
  · have hz : μ U=0 := (measure_congr hnull).trans (measure_empty)
    apply (hpos (measure_mono_null (s := S) (t := U) ?_ hz)).elim
    intro x hx
    exact mem_iUnion.mpr ⟨0,hx⟩
  · filter_upwards [ae_eq_univ.mp hfull] with x hx
    simpa only [U,mem_iUnion,mem_preimage] using hx

theorem ae_visits_unbounded_return_levels
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) {S : Set Y} (hS : MeasurableSet S)
    (htail : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ μ (firstReturnLevel T S n) ≠ 0) :
    ∀ᵐ x ∂μ, ∀ N : ℕ, ∃ k n : ℕ, N ≤ n ∧ T^[k] x ∈ firstReturnLevel T S n := by
  apply ae_all_iff.mpr
  intro N
  obtain ⟨n,hn,hpos⟩ := htail N
  filter_upwards [ae_future_visit_of_positive μ hT
    (measurableSet_firstReturnLevel hT.measurable hS n) hpos] with x hx
  obtain ⟨k,hk⟩ := hx
  exact ⟨k,n,hn,hk⟩

end DukePrimeDegree

end

end OAI
