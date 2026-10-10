import OAI.Geometry.RCD.Coordinates.NormalizedL1FromL2

namespace OAI

/-! # Bounded tests preserve the identified local energy -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem weighted_integral_difference_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Ω : ℕ → Set X) (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (f g θ : ℕ → X → ℝ)
    (hf : ∀ k, IntegrableOn (f k) (Ω k) μ) (hg : ∀ k, IntegrableOn (g k) (Ω k) μ)
    (hθ : ∀ k, AEStronglyMeasurable (θ k) (μ.restrict (Ω k)))
    {B : ℝ} (hbound : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), |θ k x| ≤ B)
    (hlim : Tendsto (fun k => c k*∫ x in Ω k, |f k x-g k x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => c k*(∫ x in Ω k, θ k x*f k x ∂μ)-
      c k*(∫ x in Ω k, θ k x*g k x ∂μ)) atTop (𝓝 0) := by
  have hi (k : ℕ) (u : X → ℝ) (hu : IntegrableOn u (Ω k) μ) :
      IntegrableOn (fun x => θ k x*u x) (Ω k) μ :=
    hu.bdd_mul (hθ k) (by simpa only [Real.norm_eq_abs] using hbound k)
  have hb (k : ℕ) : ‖c k*(∫ x in Ω k, θ k x*f k x ∂μ)-
      c k*(∫ x in Ω k, θ k x*g k x ∂μ)‖ ≤ B*(c k*∫ x in Ω k, |f k x-g k x| ∂μ) := by
    rw [← mul_sub,← integral_sub (hi k (f k) (hf k)) (hi k (g k) (hg k))]
    have he : (fun x => θ k x*f k x-θ k x*g k x) = (fun x => θ k x*(f k x-g k x)) := by
      funext x
      ring
    rw [he,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hc k)]
    have hI : |∫ x in Ω k, θ k x*(f k x-g k x) ∂μ| ≤
        B*∫ x in Ω k, |f k x-g k x| ∂μ := by
      calc
        _ ≤ ∫ x in Ω k, |θ k x*(f k x-g k x)| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ x in Ω k, B*|f k x-g k x| ∂μ := by
          apply integral_mono_ae (hi k _ ((hf k).sub (hg k))).abs (((hf k).sub (hg k)).abs.const_mul B)
          filter_upwards [hbound k] with x hx
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        _ = _ := integral_const_mul _ _
    exact (mul_le_mul_of_nonneg_left hI (hc k)).trans_eq (by ring)
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using hlim.const_mul B

end RegularPointCoordinates

end

end OAI
