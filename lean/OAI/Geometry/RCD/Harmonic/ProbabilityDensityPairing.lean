import Mathlib

namespace OAI

/-! # Bounded pairings against an actual probability density -/

open Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem probability_density_pairing_bound {ρ z : X → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x)))]
    {B : ℝ} (hz : ∀ᵐ x ∂μ, |z x| ≤ B) :
    |∫ x, z x*ρ x ∂μ| ≤ B := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (ρ x))
  have hν : ∀ᵐ x ∂ν, ‖z x‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using
      hz.filter_mono (withDensity_absolutelyContinuous μ _).ae_le
  have hb := norm_integral_le_of_norm_le_const hν
  have he : (∫ x, z x ∂ν) = ∫ x, z x*ρ x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hρ0 _),smul_eq_mul,mul_comm]
  rw [he,Real.norm_eq_abs] at hb
  simpa only [ν,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using hb

end RegularPointCoordinates

end

end OAI
