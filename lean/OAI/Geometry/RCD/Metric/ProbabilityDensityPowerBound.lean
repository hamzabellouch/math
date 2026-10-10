import OAI.Geometry.RCD.Harmonic.ProbabilityDensityPairing

namespace OAI

/-! # Integer moments of a bounded probability density -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem probability_density_power_bound {ρ : X → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x)))]
    (A : ℝ≥0) (hA : ∀ᵐ x ∂μ, |ρ x| ≤ A) (n : ℕ) :
    (∫ x, (ρ x)^(n+1) ∂μ) ≤ (A:ℝ)^n := by
  have hh := probability_density_pairing_bound μ hρ hρ0
    (B := (A:ℝ)^n) (z := fun x => (ρ x)^n) (by
      filter_upwards [hA] with x hx
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hx n)
  have he : (fun x => (ρ x)^(n+1)) = (fun x => (ρ x)^n*ρ x) := by
    funext x
    rw [pow_succ]
  rw [he]
  exact (le_abs_self _).trans hh

end RegularPointCoordinates

end

end OAI
