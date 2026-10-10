import OAI.MeasureTheory.Falconer.Angular.CompactStationaryAmplitude

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap ContDiff

 theorem compact_quadratic_stationary_expansion {b a z C D : ℝ} (hb : 0 < b)
    (haz : a ≤ z) (φ : 𝓢(ℝ,ℂ)) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a z) (n : ℕ)
    (h₀ : ∀ x, ‖iteratedDeriv (2*(n+1)) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)))
    (h₂ : ∀ x, ‖iteratedDeriv (2*(n+1)+2) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)+2)) :
    ‖(∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2)*φ x) -
      fresnelCoefficient b * quadraticExpansion φ n b‖ ≤
    ((Real.pi/b)^(1/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ))) *
      ((C*(z-a)*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
        C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹) := by
  apply (quadratic_stationary_expansion_L1 hb φ n).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ => by positivity))
  exact add_le_add (compact_fourierDerivativeL1_bound φ haz hs _ h₀)
    (compact_fourierDerivativeL1_bound φ haz hs _ h₂)

 theorem compact_quadratic_derivative_scale {a z C D : ℝ} (haz : a ≤ z)
    (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) :
    C*(z-a)*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
      C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2) ≤
    (C*(z-a)*((2*Real.pi)^(2*(n+1)))⁻¹ +
      C*(z-a)*((2*Real.pi)^(2*(n+1)+2))⁻¹) * D^(2*(n+1)+2) := by
  have hp : D^(2*(n+1)) ≤ D^(2*(n+1)+2) := pow_le_pow_right₀ hD (by omega)
  calc
    _ ≤ C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)) +
      C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2) := by
      exact add_le_add
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (sub_nonneg.mpr haz)))
          (show 0 ≤ (2 * Real.pi) ^ (2 * (n + 1)) by positivity)) le_rfl
    _ = _ := by ring

end PlanarFalconer

end OAI
