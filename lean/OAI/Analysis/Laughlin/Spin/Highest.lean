import Mathlib.Data.Nat.Factorial.Basic
import OAI.Analysis.Laughlin.Spin.HighestSpace

namespace OAI

namespace Laughlin.Spin

theorem highestUnit_div_eq_raw (A B z p q : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    highestUnit A B z p / highestUnit A B z q =
      highestRaw A B z p / highestRaw A B z q := by
  unfold highestUnit
  exact div_div_div_cancel_right₀ (ne_of_gt (highestNorm_pos A B z hA hB)) _ _

theorem source_highest_ratio (Q z p : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hp : p < z) :
    highestUnit (2*Q-2) Q z (p+1) / highestUnit (2*Q-2) Q z p =
      -Real.sqrt (((z : ℝ)-p)*((Q : ℝ)-z+p+1) /
        (((p : ℝ)+1)*(2*(Q : ℝ)-2-p))) := by
  rw [highestUnit_ratio (2*Q-2) Q z p (by omega) hz hp]
  unfold ladder
  rw [← Real.sqrt_div (by positivity)]
  have h₁ : ((z-p-1 : ℕ) : ℝ)+1 = (z : ℝ)-p := by
    rw [Nat.cast_sub (by omega : 1 ≤ z-p),Nat.cast_sub (by omega : p ≤ z)]
    push_cast; ring
  have h₂ : ((Q-(z-p-1) : ℕ) : ℝ) = (Q : ℝ)-z+p+1 := by
    rw [Nat.cast_sub (by omega : z-p-1 ≤ Q),Nat.cast_sub (by omega : 1 ≤ z-p),
      Nat.cast_sub (by omega : p ≤ z)]
    push_cast; ring
  have h₃ : ((2*Q-2-p : ℕ) : ℝ) = 2*(Q : ℝ)-2-p := by
    rw [Nat.cast_sub (by omega : p ≤ 2*Q-2),Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast; ring
  rw [h₁,h₂,h₃]

theorem highest_end_ratio (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    highestUnit A B z z / highestUnit A B z 0 =
      (-1 : ℝ)^z * Real.sqrt ((B.choose z : ℝ)/(A.choose z : ℝ)) := by
  rw [highestUnit_div_eq_raw A B z z 0 hA hB,highestRaw_zero]
  simp only [highestRaw,le_refl,ite_true,Nat.choose_self,Nat.sub_self,
    Nat.choose_zero_right,Nat.cast_one,mul_one]
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,one_mul,inv_inv]
  ring

theorem highest_penultimate_ratio (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hz : 1 ≤ z) :
    highestUnit A B z (z-1) / highestUnit A B z 0 =
      (-1 : ℝ)^(z-1) * (z : ℝ) *
        Real.sqrt ((B.choose z : ℝ)/((A.choose (z-1) : ℝ)*B)) := by
  rw [highestUnit_div_eq_raw A B z (z-1) 0 hA hB,highestRaw_zero]
  simp only [highestRaw,ite_eq_left (show z-1 ≤ z by omega)]
  rw [show z-(z-1)=1 by omega,Nat.choose_one_right,
    Nat.choose_symm hz,Nat.choose_one_right]
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,one_mul,inv_inv]
  ring

theorem choose_ratio_descFactorial (A B z : ℕ) :
    (B.choose z : ℝ)/(A.choose z : ℝ) =
      (B.descFactorial z : ℝ)/(A.descFactorial z : ℝ) := by
  simp only [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  rw [mul_div_mul_left _ _ (by positivity : (z.factorial : ℝ) ≠ 0)]

theorem source_highest_end_ratio (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    highestUnit (2*Q-2) Q z z / highestUnit (2*Q-2) Q z 0 =
      (-1 : ℝ)^z * Real.sqrt ((Q.descFactorial z : ℝ)/((2*Q-2).descFactorial z : ℝ)) := by
  rw [highest_end_ratio _ _ _ (by omega) hz,choose_ratio_descFactorial]

end Laughlin.Spin

end OAI
