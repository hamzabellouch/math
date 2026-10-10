import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaDecay

namespace OAI

/-! Exponential bounds for the normalized angular heat kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma power_exp_bound {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x^n*Real.exp (-b*x) ≤ (n.factorial:ℝ)/b^n := by
  have hs := Real.pow_div_factorial_le_exp (b*x) (mul_nonneg hb.le hx) n
  have hm := mul_le_mul_of_nonneg_right
    ((div_le_iff₀ (show 0 < (n.factorial:ℝ) by positivity)).mp hs)
    (Real.exp_pos (-b*x)).le
  have he : Real.exp (b*x)*(n.factorial:ℝ)*Real.exp (-b*x) = n.factorial := by
    calc
      _ = (n.factorial:ℝ)*(Real.exp (b*x)*Real.exp (-b*x)) := by ring
      _ = _ := by rw [←Real.exp_add,show b*x + -b*x = 0 by ring,Real.exp_zero,mul_one]
  rw [he,mul_pow] at hm
  apply (le_div_iff₀ (pow_pos hb n)).mpr
  convert hm using 1
  ring

lemma rpow_exp_half_bound {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      x^κ*Real.exp (-x) ≤ C*Real.exp (-x/2) := by
  let n : ℕ := ⌈κ⌉₊
  let C : ℝ := 1+(n.factorial:ℝ)/(1/2:ℝ)^n
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩
  intro x hx
  have hbound : x^κ*Real.exp (-(1/2)*x) ≤ C := by
    by_cases hx1 : x ≤ 1
    · have hr := Real.rpow_le_one hx hx1 hκ
      have he : Real.exp (-(1/2)*x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      exact (show x^κ*Real.exp (-(1/2)*x) ≤ 1 by
        simpa only [one_mul] using mul_le_mul hr he (Real.exp_pos _).le zero_le_one).trans hC
    · have hr : x^κ ≤ x^n := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (Nat.le_ceil κ)
      exact (mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le).trans
        ((power_exp_bound (by norm_num : (0:ℝ) < 1/2) n x hx).trans (by dsimp [C]; linarith))
  calc
    x^κ*Real.exp (-x) = (x^κ*Real.exp (-(1/2)*x))*Real.exp (-x/2) := by
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le

end CubicFirstMoment

end

end OAI
