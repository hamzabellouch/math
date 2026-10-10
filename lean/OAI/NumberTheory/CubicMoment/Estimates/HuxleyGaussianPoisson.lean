import OAI.NumberTheory.CubicMoment.Estimates.HuxleyPhase
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

namespace OAI

/-! One-dimensional Gaussian Poisson identities for the coordinate majorant. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

lemma summable_integer_quadratic_exp (A B C : ℂ) (hA : A.re < 0) :
    Summable (fun n : ℤ => Complex.exp (A*(n:ℂ)^2+B*(n:ℂ)+C)) := by
  have hdec := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hA B (-2)).isBigO
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow (show (1:ℝ) < 2 by norm_num))
    (hdec.comp_tendsto Int.tendsto_coe_cofinite)
  have hm := hs.mul_right (Complex.exp C)
  convert hm using 1
  ext n
  simp only [Function.comp_apply,Complex.ofReal_intCast,← Complex.exp_add]

lemma gaussian_coordinate_poisson {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    (∑' n : ℤ, Complex.exp ((-Real.pi*a*(n:ℝ)^2:ℝ):ℂ)*
      Complex.exp (((2*Real.pi*ξ*(n:ℝ):ℝ):ℂ)*Complex.I)) =
    ((1/Real.sqrt a:ℝ):ℂ)*(∑' m : ℤ,
      Complex.exp ((-Real.pi/a*((m:ℝ)-ξ)^2:ℝ):ℂ)) := by
  have hp : 1/(a:ℂ)^(1/2:ℂ) = ((1/Real.sqrt a:ℝ):ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow ha.le,← Real.sqrt_eq_rpow,
      Complex.ofReal_div,Complex.ofReal_one]
  calc
    _ = ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)*(a:ℂ)*(n:ℂ)^2+
        2*(Real.pi:ℂ)*(Complex.I*(ξ:ℂ))*(n:ℂ)) := by
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [Complex.tsum_exp_neg_quadratic (a := (a:ℂ)) (by simpa using ha),hp]
      congr 1
      apply tsum_congr
      intro m
      congr 1
      push_cast
      ring_nf
      norm_num

end CubicFirstMoment

end

end OAI
