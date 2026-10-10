import OAI.Analysis.Laughlin.Spin.GeneralSpinAction
import OAI.Analysis.Laughlin.Spin.LadderMatrix

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators

noncomputable def spinBinomialWeight (Q : ℕ) (p : Fin (Q+1)) : ℂ :=
  (Real.sqrt (Q.choose p.val : ℝ) : ℂ)

theorem spinBinomialWeight_ne_zero (Q : ℕ) (p : Fin (Q+1)) : spinBinomialWeight Q p ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ p.isLt)

theorem spinBinomialWeight_step (Q : ℕ) (p : Fin Q) :
    spinBinomialWeight Q p.succ * ((p.val : ℂ)+1) =
      spinBinomialWeight Q p.castSucc * (Spin.ladder Q p.val : ℂ) := by
  have hr : Real.sqrt (Q.choose (p.val+1) : ℝ)*((p.val : ℝ)+1) =
      Real.sqrt (Q.choose p.val : ℝ)*Spin.ladder Q p.val := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq Q p.val)
    push_cast at hc
    have he : (Real.sqrt (Q.choose (p.val+1) : ℝ)*((p.val : ℝ)+1))^2 =
        (Real.sqrt (Q.choose p.val : ℝ)*Spin.ladder Q p.val)^2 := by
      unfold Spin.ladder
      rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
      linear_combination ((p.val : ℝ)+1)*hc
    have h1 : 0 ≤ Real.sqrt (Q.choose (p.val+1) : ℝ)*((p.val : ℝ)+1) := by positivity
    have h2 : 0 ≤ Real.sqrt (Q.choose p.val : ℝ)*Spin.ladder Q p.val := by
      unfold Spin.ladder; positivity
    nlinarith only [he,h1,h2]
  simpa [spinBinomialWeight] using congrArg Complex.ofReal hr

end Laughlin.Rotation

end OAI
