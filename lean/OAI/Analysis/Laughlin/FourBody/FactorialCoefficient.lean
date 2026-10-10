import OAI.Analysis.Laughlin.FourBody.Basic
import OAI.Analysis.Laughlin.FourBody.CoefficientLimit
import OAI.Analysis.Laughlin.Polynomial.SourceEqualSpinPolynomial

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_factorial_coefficient (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) (hr : r ≤ j+k) :
    fourBodyLimitCoefficient r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) * (Certificate.V r D T p j k : ℝ) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  have hi : r+(j+k-r)=j+k := by omega
  have ho : (D-r)+(T-D)=T-r := by omega
  have hk : j+k-j=k := by omega
  have hb : T-r-p=j+k-r := by omega
  rw [fourBodyLimitCoefficient,ite_eq_left hr,
    equalSpin_polynomialCoefficient _ r (j+k-r) j (by omega),
    equalSpin_polynomialCoefficient _ (D-r) (T-D) p (by omega)]
  rw [hi,ho,hk,hb]
  simp only [Certificate.V,ite_eq_left hr,Int.cast_mul]
  rw [pow_add]
  field_simp [ne_of_gt (sqrtFactorial_pos r),ne_of_gt (sqrtFactorial_pos (D-r)),
    ne_of_gt (sqrtFactorial_pos (T-D)),ne_of_gt (sqrtFactorial_pos (j+k-r))]
  ring

end Laughlin.Spin

end OAI
