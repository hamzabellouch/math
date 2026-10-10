import Mathlib.Analysis.Complex.Exponential
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericWitnessGeometry

namespace OAI

namespace Ostmann.QuadraticCenter

lemma numeric_witness_numerator_identity {M X S Y K C : ℝ}
    (hX : 0<X) (hS : 0<S) (hY : 0<Y) (hC : 0<C)
    (hscale : Y^2 = (M/X)/S) :
    M*Real.exp (8*K)/(Y*(Real.exp (-K)/(10*C)))^2 =
      100*C^2*X*S*Real.exp (10*K) := by
  have hM : M = Y^2*X*S := by
    rw [div_div] at hscale
    have h := (eq_div_iff (mul_ne_zero hX.ne' hS.ne')).mp hscale
    nlinarith only [h]
  have he : Real.exp (8*K) = Real.exp (-K)^2*Real.exp (10*K) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  rw [he,hM]
  field_simp
  ring

end Ostmann.QuadraticCenter

end OAI
