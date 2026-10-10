import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Absolute integral convergence makes a pointwise scalar series integrable. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter ENNReal
open scoped ENNReal Topology

theorem scalar_integrable_series {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {μ : Measure X} {F : ι → X → ℝ} {f : X → ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ))
    (hf : ∀ x, HasSum (fun i => F i x) (f x)) : Integrable f μ := by
  classical
  have hm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset ι => (integrable_finsetSum s (fun i _ => hF i)).aestronglyMeasurable)
      (Eventually.of_forall hf)
  have he (i : ι) : (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF i).norm, coe_nnreal_eq, coe_nnnorm]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (F i x)))]
  have hne : (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ) ≠ ∞ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs.abs)
  refine ⟨hm, lt_of_le_of_lt (lintegral_mono (g := fun x => ∑' i, ‖F i x‖ₑ)
    (fun x => ?_)) ?_⟩
  · rw [← (hf x).tsum_eq]
    exact enorm_tsum_le_tsum_enorm
  · rw [lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)]
    exact hne.lt_top

end PositiveEinsteinFour.Geometry

end OAI
