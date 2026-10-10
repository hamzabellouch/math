import OAI.NumberTheory.CubicMoment.Estimates.DominantSmoothPower

namespace OAI

/-! The cubic-sieve envelope for balanced conductor variables. -/
noncomputable section
namespace CubicFirstMoment

lemma balanced_cubic_envelope :
    ∃ K : ℝ, 0 < K ∧ ∀ N Z J Y : ℝ, 1 ≤ Y → 1 ≤ N → 1 ≤ Z → 1 ≤ J →
      N ≤ Y^(1/2:ℝ) → Z ≤ Y^(101/100:ℝ) → J ≤ Y^(1/2:ℝ) →
      Z*(N*(2*J))^(1/100:ℝ)*(N+2*J+(N*(2*J))^(2/3:ℝ)) ≤ K*Y^(17/10:ℝ) := by
  let K : ℝ := (2:ℝ)^(1/100:ℝ)*(3+(2:ℝ)^(2/3:ℝ))
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro N Z J Y hY hN hZ hJ hNY hZY hJY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ : N*(2*J) ≤ 2*Y^(1:ℝ) := by
    calc
      _ ≤ Y^(1/2:ℝ)*(2*Y^(1/2:ℝ)) := by gcongr
      _ = 2*(Y^(1/2:ℝ)*Y^(1/2:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num
  have hpow (s : ℝ) (hs : 0 ≤ s) :
      (N*(2*J))^s ≤ (2:ℝ)^s*Y^((1)*s) := by
    calc
      _ ≤ (2*Y^(1:ℝ))^s := Real.rpow_le_rpow (by positivity) hQ hs
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hY0.le _),
        ← Real.rpow_mul hY0.le]
  have hsmall := hpow (1/100) (by norm_num)
  have hlarge := hpow (2/3) (by norm_num)
  norm_num at hsmall hlarge
  have hnF : N ≤ Y^(2/3:ℝ) := hNY.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))
  have hjF : J ≤ Y^(2/3:ℝ) := hJY.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))
  have hF : N+2*J+(N*(2*J))^(2/3:ℝ) ≤
      (3+(2:ℝ)^(2/3:ℝ))*Y^(2/3:ℝ) := by nlinarith
  calc
    _ ≤ Y^(101/100:ℝ)*((2:ℝ)^(1/100:ℝ)*Y^(1/100:ℝ))*
        ((3+(2:ℝ)^(2/3:ℝ))*Y^(2/3:ℝ)) := by
      exact mul_le_mul (mul_le_mul hZY hsmall (by positivity) (by positivity)) hF
        (by positivity) (by positivity)
    _ = K*Y^((101/100:ℝ)+1/100+2/3) := by
      dsimp [K]
      rw [Real.rpow_add hY0,Real.rpow_add hY0]
      ring
    _ ≤ K*Y^(17/10:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by dsimp [K]; positivity)

end CubicFirstMoment

end

end OAI
