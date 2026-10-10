import OAI.Geometry.RCD.Sobolev.ScaledGammaError

namespace OAI

/-! # Vanishing constant-source errors in compact cutoff tests -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem normalized_source_error_tendsto (μ : ℕ → Measure X)
    [∀ k, IsFiniteMeasure (μ k)] (hmass : ∀ k, 0<(μ k).real univ)
    (z v : ℕ → X → ℝ) (a : ℕ → ℝ) {A B : ℝ} (hA : 0≤A)
    (ha : ∀ᶠ k in atTop, |a k|≤A)
    (hv : ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |v k x|≤B)
    (hz : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |z k x|≤δ) :
    Tendsto (fun k => a k*((μ k).real univ)⁻¹*
      ∫ x, (v k x)^2*z k x ∂μ k) atTop (𝓝 0) := by
  have hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |a k*(v k x)^2|≤A*B^2 := by
    filter_upwards [ha,hv] with k hak hvk
    filter_upwards [hvk] with x hvx
    rw [abs_mul,abs_pow]
    exact mul_le_mul hak (pow_le_pow_left₀ (abs_nonneg _) hvx 2) (sq_nonneg _) hA
  have ht := normalized_product_error_tendsto μ hmass z (fun k x => a k*(v k x)^2)
    (mul_nonneg hA (sq_nonneg B)) hb hz
  convert ht using 1
  funext k
  have he : (fun x => z k x*(a k*(v k x)^2))=fun x => a k*((v k x)^2*z k x) := by
    funext x
    ring
  rw [he,integral_const_mul]
  ring

end RegularPointCoordinates

end

end OAI
