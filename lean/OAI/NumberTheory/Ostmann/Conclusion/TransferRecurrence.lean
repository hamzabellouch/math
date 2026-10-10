import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Ostmann.Conclusion

def transferBudget (B₀ m c : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ)^j * B₀ * m + ((2 : ℝ)^j - 1) * (c + Real.log 2)

@[simp] theorem transferBudget_zero (B₀ m c : ℝ) :
    transferBudget B₀ m c 0 = B₀ * m := by simp [transferBudget]

theorem transferBudget_succ (B₀ m c : ℝ) (j : ℕ) :
    transferBudget B₀ m c (j + 1) =
      2 * transferBudget B₀ m c j + c + Real.log 2 := by
  simp only [transferBudget, pow_succ]
  ring

theorem transferBudget_lt (B₀ m c : ℝ) (hm : 0 < m)
    (hc : c + Real.log 2 ≤ m) (j : ℕ) :
    transferBudget B₀ m c j < (B₀ + 3) * (2 : ℝ)^j * m := by
  have hp : 1 ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hp)
  have hpm : 0 < (2 : ℝ)^j * m := mul_pos (by positivity) hm
  dsimp [transferBudget]
  nlinarith

private theorem exp_half_square (t c : ℝ) :
    (1 / 2 : ℝ) * Real.exp (-c) * (Real.exp (-t))^2 =
      Real.exp (-(2*t+c+Real.log 2)) := by
  rw [show -(2*t+c+Real.log 2) = -c + (-t + -t) - Real.log 2 by ring]
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_add, Real.exp_add]
  ring

theorem transfer_step {B m c x y D : ℝ} {j : ℕ}
    (hm : 0 < m) (hc : c + Real.log 2 ≤ m)
    (hcoarse : Real.exp (-B * (2 : ℝ)^j * m) ≤ |x|)
    (hdiagonal : D ≤ Real.exp (-(2*B+3) * (2 : ℝ)^j * m))
    (htransfer : Real.exp (-c) * |x|^2 ≤ D + |y|) :
    (1/2 : ℝ) * Real.exp (-c) * |x|^2 ≤ |y| := by
  have hp : 1 ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hpm : m ≤ (2 : ℝ)^j * m := by nlinarith
  have hexp : Real.exp (-(2*B+3) * (2 : ℝ)^j * m) ≤
      Real.exp (-(2*(B*(2 : ℝ)^j*m)+c+Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsquare : (Real.exp (-(B*(2 : ℝ)^j*m)))^2 ≤ |x|^2 := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    simpa only [neg_mul] using hcoarse
  have hscale := mul_le_mul_of_nonneg_left hsquare
      (show 0 ≤ (1/2 : ℝ) * Real.exp (-c) by positivity)
  rw [← exp_half_square] at hexp
  have hD : D ≤ (1/2 : ℝ) * Real.exp (-c) * |x|^2 :=
    hdiagonal.trans (hexp.trans hscale)
  linarith

theorem transfer_exact_lower (η D : ℕ → ℝ) (B₀ m c : ℝ) (hm : 0 < m)
    (hc : c + Real.log 2 ≤ m) (k : ℕ)
    (hinitial : Real.exp (-B₀*m) ≤ |η 0|)
    (hdiagonal : ∀ j < k,
      D j ≤ Real.exp (-(2*(B₀+3)+3) * (2 : ℝ)^j*m))
    (htransfer : ∀ j < k, Real.exp (-c) * |η j|^2 ≤ D j + |η (j+1)|) :
    ∀ j ≤ k, Real.exp (-transferBudget B₀ m c j) ≤ |η j| := by
  intro j hj
  induction j with
  | zero => simpa only [transferBudget_zero, neg_mul] using hinitial
  | succ j ih =>
    have hjk : j < k := by omega
    have ih := ih (by omega)
    have coarse : Real.exp (-(B₀+3) * (2 : ℝ)^j*m) ≤ |η j| := by
      refine (Real.exp_le_exp.mpr ?_).trans ih
      have h := transferBudget_lt B₀ m c hm hc j
      nlinarith
    have step := transfer_step hm hc coarse (hdiagonal j hjk) (htransfer j hjk)
    have hsquare := pow_le_pow_left₀ (Real.exp_pos _).le ih 2
    have hscale := mul_le_mul_of_nonneg_left hsquare
      (show 0 ≤ (1/2 : ℝ)*Real.exp (-c) by positivity)
    rw [exp_half_square, ← transferBudget_succ] at hscale
    exact hscale.trans step

theorem transfer_exact_log {η : ℝ} {T : ℝ}
    (h : Real.exp (-T) ≤ |η|) : η ≠ 0 ∧ -Real.log |η| ≤ T := by
  have hpos : 0 < |η| := (Real.exp_pos _).trans_le h
  constructor
  · exact abs_pos.mp hpos
  · have hl := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp] at hl
    linarith

theorem incompatible_final_rates {x B r m : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hlower : Real.exp (-2*B*r*m) ≤ |x|^2)
    (hupper : |x|^2 ≤ Real.exp (-(2*B+1)*r*m)) : False := by
  have h := Real.exp_le_exp.mp (hlower.trans hupper)
  have : 0 < r*m := mul_pos hr hm
  nlinarith

end Ostmann.Conclusion

end

end OAI
