import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # Differentiation on a compact spatial cylinder -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem compact_integral_hasDerivAt {a b t : ℝ} (ht : t ∈ Ioo a b)
    {Ω : Set X} (hΩ : IsCompact Ω) (F G : ℝ → X → ℝ)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Ω))
    (hG : ContinuousOn (Function.uncurry G) (Icc a b ×ˢ Ω))
    (hder : ∀ s ∈ Ioo a b, ∀ x ∈ Ω, HasDerivAt (fun r => F r x) (G s x) s) :
    HasDerivAt (fun s => ∫ x in Ω, F s x ∂μ) (∫ x in Ω, G t x ∂μ) t := by
  have hFs (s : ℝ) (hs : s ∈ Icc a b) : ContinuousOn (F s) Ω :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨hs,hx⟩)
  have hGs (s : ℝ) (hs : s ∈ Icc a b) : ContinuousOn (G s) Ω :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨hs,hx⟩)
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hΩ).exists_bound_of_continuousOn hG
  have hfin : IsFiniteMeasure (μ.restrict Ω) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hΩ.measure_lt_top⟩
  have hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (μ.restrict Ω) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (hFs s (Ioo_subset_Icc_self hs)).aestronglyMeasurable hΩ.measurableSet
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
    hm ((hFs t (Ioo_subset_Icc_self ht)).integrableOn_compact hΩ)
    ((hGs t (Ioo_subset_Icc_self ht)).aestronglyMeasurable hΩ.measurableSet)
    (by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      intro s hs
      exact hM (s,x) ⟨Ioo_subset_Icc_self hs,hx⟩)
    (integrable_const M)
    (by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      exact fun s hs => hder s hs x hx)).2

end RegularPointCoordinates

end

end OAI
