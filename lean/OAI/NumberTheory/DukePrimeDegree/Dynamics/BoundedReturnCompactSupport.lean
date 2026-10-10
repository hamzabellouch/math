import OAI.NumberTheory.DukePrimeDegree.Dynamics.ReturnTowerCoverage
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Bounded section returns force compact support

This is the compact case in the return-partition construction: if a
relatively compact section has essentially bounded positive return time,
its finitely many translates support the whole ergodic measure.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

theorem ae_mem_bounded_return_translates
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) (hpos : μ S ≠ 0)
    (N : ℕ) (hbound : ∀ n, N ≤ n → μ (firstReturnLevel T S n)=0) :
    ∀ᵐ x ∂μ, ∃ j < N, x ∈ T^[j] '' S := by
  have hEi (j : ℕ) : MeasurableEmbedding (T^[j]) := by
    induction j with
    | zero => exact MeasurableEmbedding.id
    | succ j ih =>
        rw [Function.iterate_succ]
        exact ih.comp hE
  have hzero (p : Σ n : ℕ, Fin (n+1)) :
      N ≤ p.1 → μ (firstReturnTower T S p)=0 := by
    intro hp
    change μ (T^[p.2.val] '' firstReturnLevel T S p.1)=0
    rw [←(hT.toMeasurePreserving.iterate p.2.val).map_eq]
    rw [Measure.map_apply (hT.measurable.iterate p.2.val)
      ((hEi p.2.val).measurableSet_image.mpr
        (measurableSet_firstReturnLevel hT.measurable hS p.1))]
    rw [(hEi p.2.val).injective.preimage_image]
    exact hbound p.1 hp
  have havoid (p : Σ n : ℕ, Fin (n+1)) :
      ∀ᵐ x ∂μ, N ≤ p.1 → x ∉ firstReturnTower T S p := by
    by_cases hp : N ≤ p.1
    · exact (measure_eq_zero_iff_ae_notMem.mp (hzero p hp)).mono (fun _ hx _ => hx)
    · exact ae_of_all _ (fun _ h => (hp h).elim)
  filter_upwards [ae_mem_firstReturnTower μ hT hE hS hpos,ae_all_iff.mpr havoid]
    with x hx ha
  obtain ⟨⟨n,j⟩,y,hy,hxy⟩ := hx
  have hn : n < N := by
    by_contra hn
    exact ha ⟨n,j⟩ (Nat.le_of_not_gt hn) ⟨y,hy,hxy⟩
  exact ⟨j.val,lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) hn,y,hy.1,hxy⟩

theorem exists_compact_support_of_bounded_returns
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T) (hcont : Continuous T)
    {S : Set Y} (hS : MeasurableSet S) (hpos : μ S ≠ 0)
    (hcompact : IsCompact (closure S))
    (N : ℕ) (hbound : ∀ n, N ≤ n → μ (firstReturnLevel T S n)=0) :
    ∃ K : Set Y, IsCompact K ∧ μ K=1 := by
  let K := ⋃ j : Fin N, T^[j.val] '' closure S
  have hK : IsCompact K := isCompact_iUnion
    (fun j => hcompact.image (hcont.iterate j.val))
  refine ⟨K,hK,?_⟩
  have hfull : ∀ᵐ x ∂μ, x ∈ K := by
    filter_upwards [ae_mem_bounded_return_translates μ hT hE hS hpos N hbound]
      with x hx
    obtain ⟨j,hj,y,hy,hxy⟩ := hx
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,y,subset_closure hy,hxy⟩
  exact (measure_congr (ae_eq_univ.mpr hfull)).trans (measure_univ)

end DukePrimeDegree

end

end OAI
