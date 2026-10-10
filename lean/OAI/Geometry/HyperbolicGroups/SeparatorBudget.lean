import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion

/-- A charging potential for the recursive separator construction. The
constant is deliberately inessential: only existence of K is required. -/
def budget (c K n : ℝ) : ℝ := 16 * c * n / Real.sqrt K - 8 * c * Real.sqrt n

lemma budget_nonneg {c K n : ℝ} (hc : 0 ≤ c) (hK : 0 < K)
    (hn : 0 ≤ n) (hlow : K ≤ 4 * n) : 0 ≤ budget c K n := by
  have hk := Real.sqrt_pos.2 hK
  have hx := Real.sqrt_nonneg n
  have hks := Real.sq_sqrt hK.le
  have hxs := Real.sq_sqrt hn
  have hbound : Real.sqrt K ≤ 2 * Real.sqrt n := by nlinarith
  have hprod : Real.sqrt n * Real.sqrt K ≤ 2 * n := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg n) (sub_nonneg.mpr hbound)]
  have hmul := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8*c by positivity)
  unfold budget
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hk).mpr
  nlinarith

lemma sqrt_split_gain {n s a b : ℝ} (hn : 0 ≤ n) (ha : n/4 ≤ a) (hb : n/4 ≤ b)
    (hs : s ≤ n/12) (hsum : s+a+b=n) :
    (9/8 : ℝ) * Real.sqrt n ≤ Real.sqrt a + Real.sqrt b := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have hb0 : 0 ≤ b := le_trans (by positivity) hb
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have hz := Real.sqrt_nonneg n
  have hxs := Real.sq_sqrt ha0
  have hys := Real.sq_sqrt hb0
  have hzs := Real.sq_sqrt hn
  have hzx : Real.sqrt n / 2 ≤ Real.sqrt a := by nlinarith
  have hzy : Real.sqrt n / 2 ≤ Real.sqrt b := by nlinarith
  have hp := mul_le_mul hzx hzy (by positivity : 0 ≤ Real.sqrt n / 2) hx
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith

lemma split_numeric {c K n s a b : ℝ} (hc : 0 ≤ c) (hn : 0 ≤ n)
    (hK : 144*c^2 ≤ K) (hKn : K ≤ n) (hsep : s ≤ c * Real.sqrt n)
    (hsum : s+a+b=n) (ha : 3*a ≤ 2*n) (hb : 3*b ≤ 2*n) :
    s ≤ n/12 ∧ n/4 ≤ a ∧ n/4 ≤ b := by
  have hz := Real.sqrt_nonneg n
  have hzs := Real.sq_sqrt hn
  have hzc : 12*c ≤ Real.sqrt n := by
    apply (mul_self_le_mul_self_iff (mul_nonneg (by norm_num) hc) hz).mpr
    nlinarith
  have hs : s ≤ n/12 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg n) (sub_nonneg.mpr hzc)]
  exact ⟨hs,by linarith,by linarith⟩

lemma budget_step {c K n s a b : ℝ} (hc : 0 ≤ c) (hK : 0 < K) (hn : 0 ≤ n)
    (hs0 : 0 ≤ s) (ha : n/4 ≤ a) (hb : n/4 ≤ b)
    (hs : s ≤ n/12) (hsep : s ≤ c * Real.sqrt n) (hsum : s+a+b=n) :
    s + budget c K a + budget c K b ≤ budget c K n := by
  have hg := sqrt_split_gain hn ha hb hs hsum
  have hp : s ≤ 8*c*(Real.sqrt a+Real.sqrt b-Real.sqrt n) := by
    have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ 8*c by positivity)
    nlinarith
  have hnon : 0 ≤ 16*c*s/Real.sqrt K := by positivity
  have hid : s + budget c K a + budget c K b = budget c K n +
      (s-8*c*(Real.sqrt a+Real.sqrt b-Real.sqrt n)-16*c*s/Real.sqrt K) := by
    unfold budget
    rw [← hsum]
    ring
  rw [hid]
  linarith

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
