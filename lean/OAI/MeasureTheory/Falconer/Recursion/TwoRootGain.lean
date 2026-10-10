import OAI.MeasureTheory.Falconer.Estimates.PolicyRootCoefficient
import OAI.MeasureTheory.Falconer.Recursion.Entry

namespace OAI

/-! # Combining the two root bounds at the common entry depth -/

namespace Falconer

theorem two_root_normalized_gain {R C x y : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (_hx : 0 ≤ x) (hy : 0 ≤ y) (A B P Q H loss : ℝ)
    (hxbound : x ≤ C*R^(2*A-P+loss))
    (hybound : y ≤ C*R^(2*B-Q+loss)) :
    R^(-A-B+H)*Real.sqrt (x*y) ≤ C*R^(H-(P+Q)/2+loss) := by
  have hsqrt : Real.sqrt (x*y) ≤ C*R^((2*A-P+loss+2*B-Q+loss)/2) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    apply (mul_le_mul hxbound hybound hy (by positivity)).trans_eq
    rw [mul_pow,← Real.rpow_natCast (R^((2*A-P+loss+2*B-Q+loss)/2)) 2,
      ← Real.rpow_mul hR.le]
    norm_num only [Nat.cast_ofNat]
    have he : ((2*A-P+loss+2*B-Q+loss)/2)*(2:ℝ) =
        (2*A-P+loss)+(2*B-Q+loss) := by ring
    rw [he]
    calc
      _ = C^2*(R^(2*A-P+loss)*R^(2*B-Q+loss)) := by ring
      _ = _ := by rw [← Real.rpow_add hR]
  calc
    _ ≤ R^(-A-B+H)*(C*R^((2*A-P+loss+2*B-Q+loss)/2)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = C*R^((-A-B+H)+((2*A-P+loss+2*B-Q+loss)/2)) := by
      calc
        _ = C*(R^(-A-B+H)*R^((2*A-P+loss+2*B-Q+loss)/2)) := by ring
        _ = _ := by rw [← Real.rpow_add hR]
    _ = _ := by congr 2; ring

theorem two_root_gain_at_entry {R C x y : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (A B P Q H loss β error : ℝ)
    (hxbound : x ≤ C*R^(2*A-P+loss))
    (hybound : y ≤ C*R^(2*B-Q+loss))
    (hentry : H-(P+Q)/2 ≤ -β+error) :
    R^(-A-B+H)*Real.sqrt (x*y) ≤ C*R^(-β+error+loss) := by
  apply (two_root_normalized_gain (zero_lt_one.trans_le hR) hC hx hy
    A B P Q H loss hxbound hybound).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)

end Falconer

end OAI
