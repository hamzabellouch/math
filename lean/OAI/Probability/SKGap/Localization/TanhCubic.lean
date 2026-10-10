import Mathlib
import OAI.Probability.SKGap.Localization.TAPScalarTaylor

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set

lemma abs_tanh_le_abs (x : ℝ) : |tanh x| ≤ |x| := by
  simpa only [tanh_zero,sub_zero] using tanh_lipschitz_abs x 0

lemma tanh_cubic_error (x : ℝ) : |tanh x-x| ≤ |x|^3/3 := by
  let f : ℝ→ℝ := fun y=>y^3/3-y+tanh y
  have hd (y : ℝ) : HasDerivAt f (y^2-tanh y^2) y := by
    dsimp [f]
    convert! ((((hasDerivAt_id y).pow 3).div_const 3).sub (hasDerivAt_id y)).add (hasDerivAt_tanh y) using 1; simp only [id_eq]; ring
  have hm : Monotone f := monotone_of_deriv_nonneg (fun y=>(hd y).differentiableAt) (fun y=>by
    rw [(hd y).deriv]
    have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (abs_tanh_le_abs y)
    simpa only [sq_abs,sub_nonneg] using hs)
  have hp (y : ℝ) (hy : 0 ≤ y) : |tanh y-y| ≤ |y|^3/3 := by
    have h := hm hy
    have ht : tanh y ≤ y := (le_abs_self _).trans ((abs_tanh_le_abs y).trans_eq (abs_of_nonneg hy))
    rw [abs_of_nonpos (sub_nonpos.mpr ht),abs_of_nonneg hy]
    simp only [f,tanh_zero,zero_pow (by decide : (3:ℕ) ≠ 0),zero_div,sub_zero,zero_add] at h
    linarith only [h]
  rcases le_or_gt 0 x with hx | hx
  · exact hp x hx
  · have h := hp (-x) (by linarith)
    simpa only [tanh_neg,neg_sub_neg,abs_sub_comm,abs_neg] using h
end SKGap

end
end

end OAI
