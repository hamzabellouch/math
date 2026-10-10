import OAI.Geometry.RCD.Sobolev.WeightedEnergyWeightLimit

namespace OAI

/-! # Integrable pairings with uniformly bounded convergent weights -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem bounded_weight_integral_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : ℕ → X → ℝ) (v : X → ℝ)
    (hw : ∀ k, AEStronglyMeasurable (w k) μ) {M : ℝ≥0}
    (hM : ∀ k, ∀ᵐ x ∂μ, ‖w k x‖ ≤ M)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun k => w k x) atTop (𝓝 (v x)))
    (f : X → ℝ) (hf : Integrable f μ) :
    Tendsto (fun k => ∫ x, w k x*f x ∂μ) atTop (𝓝 (∫ x, v x*f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (M:ℝ)*|f x|)
  · intro k
    exact (hw k).mul hf.aestronglyMeasurable
  · exact hf.abs.const_mul M
  · intro k
    filter_upwards [hM k] with x hx
    rw [norm_mul,Real.norm_eq_abs (f x)]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  · filter_upwards [hc] with x hx
    exact hx.mul_const _

end RegularPointCoordinates

end

end OAI
