import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMellin
import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra

namespace OAI

/-! Exact frequency powers in the fixed-angular theta Mellin transform. -/
noncomputable section
namespace CubicFirstMoment

/-- The frequency multiplier produced by the derivative of order |ell|,
with its signed angular component kept explicit. -/
def cubicThetaAngularCoefficient (a : Eisenstein → ℂ) (ℓ : ℤ) (n : Eisenstein) : ℂ :=
  (‖cubicThetaFrequency n‖:ℂ)^ℓ.natAbs*theta ℓ n*a n

lemma cubicThetaAngularCoefficient_norm {a : Eisenstein → ℂ} (ℓ : ℤ)
    {n : Eisenstein} (hn : n ≠ 0) :
    ‖cubicThetaAngularCoefficient a ℓ n‖ = ‖cubicThetaFrequency n‖^ℓ.natAbs*‖a n‖ := by
  simp only [cubicThetaAngularCoefficient,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _),norm_theta hn,mul_one]

lemma cubicThetaAngular_real_power {r : ℝ} (hr : 0 < r) (k : ℕ) (s : ℂ) :
    r^k*r^(-(2*s+(k:ℂ)-1).re) = r^(-(2*s-1).re) := by
  rw [←Real.rpow_natCast,←Real.rpow_add hr]
  congr 1
  simp only [Complex.add_re,Complex.sub_re,Complex.natCast_re]
  ring

lemma cubicThetaAngular_complex_power {r : ℝ} (hr : 0 < r) (k : ℕ) (s : ℂ) :
    (r:ℂ)^k*(r:ℂ)^(-(2*s+(k:ℂ)-1)) = (r:ℂ)^(-(2*s-1)) := by
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  rw [←Complex.cpow_natCast,←Complex.cpow_add _ _ hrC]
  congr 1
  ring

/-- The growing derivative factor exactly cancels the shifted Mellin
exponent; the remaining coefficient mass is the original bounded one. -/
lemma cubicThetaAngular_weight {a : Eisenstein → ℂ} (ℓ : ℤ)
    {n : Eisenstein} (hn : n ≠ 0) (s : ℂ) :
    ‖cubicThetaAngularCoefficient a ℓ n‖*
      ‖cubicThetaFrequency n‖^(-(2*s+(ℓ.natAbs:ℂ)-1).re) =
        ‖a n‖*‖cubicThetaFrequency n‖^(-(2*s-1).re) := by
  rw [cubicThetaAngularCoefficient_norm ℓ hn]
  calc
    _ = ‖a n‖*(‖cubicThetaFrequency n‖^ℓ.natAbs*
        ‖cubicThetaFrequency n‖^(-(2*s+(ℓ.natAbs:ℂ)-1).re)) := by ring
    _ = _ := by rw [cubicThetaAngular_real_power (cubicThetaFrequency_pos hn)]

lemma cubicThetaAngular_dirichlet_term {a : Eisenstein → ℂ} (ℓ : ℤ)
    {n : Eisenstein} (hn : n ≠ 0) (s : ℂ) :
    cubicThetaAngularCoefficient a ℓ n*
      (‖cubicThetaFrequency n‖:ℂ)^(-(2*s+(ℓ.natAbs:ℂ)-1)) =
        theta ℓ n*a n*(‖cubicThetaFrequency n‖:ℂ)^(-(2*s-1)) := by
  unfold cubicThetaAngularCoefficient
  calc
    _ = (theta ℓ n*a n)*((‖cubicThetaFrequency n‖:ℂ)^ℓ.natAbs*
        (‖cubicThetaFrequency n‖:ℂ)^(-(2*s+(ℓ.natAbs:ℂ)-1))) := by ring
    _ = _ := by rw [cubicThetaAngular_complex_power (cubicThetaFrequency_pos hn)]

end CubicFirstMoment

end

end OAI
