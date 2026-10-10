import Mathlib.Tactic.FieldSimp
import OAI.Analysis.Laughlin.Asymptotics.Bound

namespace OAI

namespace Laughlin

theorem gramEigenvalueFormula_zero (Q : ℕ) : gramEigenvalueFormula Q 0 = -1 := by
  simp [gramEigenvalueFormula,fallingRatio]

theorem gramEigenvalueFormula_one (Q : ℕ) (hQ : 2 ≤ Q) : gramEigenvalueFormula Q 1 = -1 := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hd : (2*(Q : ℝ)-2) ≠ 0 := by
    have h : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hq1 : -1+(Q : ℝ) ≠ 0 := by
    have hh : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  norm_num [gramEigenvalueFormula,fallingRatio,Nat.descFactorial]
  rw [Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  ring_nf
  field_simp [hq1]
  ring

theorem descFactorial_three_real (n : ℕ) (hn : 2 ≤ n) :
    (n.descFactorial 3 : ℝ) = (n : ℝ)*(n-1)*(n-2) := by
  norm_num [Nat.descFactorial]
  rw [Nat.cast_sub hn,Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem gramEigenvalueFormula_three (Q : ℕ) (hQ : 3 ≤ Q) : gramEigenvalueFormula Q 3 = -1 := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have h : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd₀ : (2*(Q : ℝ)-2) ≠ 0 := by linarith
  have hd₁ : (2*(Q : ℝ)-2-1) ≠ 0 := by linarith
  have hd₂ : (2*(Q : ℝ)-2-2) ≠ 0 := by linarith
  have hpoly : -6+(Q : ℝ)*13-(Q : ℝ)^2*9+(Q : ℝ)^3*2 ≠ 0 := by
    have hp : 0 < ((Q : ℝ)-1)*((Q : ℝ)-2)*(2*(Q : ℝ)-3) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    nlinarith
  unfold gramEigenvalueFormula fallingRatio
  rw [descFactorial_three_real Q (by omega),descFactorial_three_real (2*Q-2) (by omega),
    Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  norm_num
  field_simp
  ring_nf
  field_simp [hpoly]
  ring

end Laughlin

end OAI
