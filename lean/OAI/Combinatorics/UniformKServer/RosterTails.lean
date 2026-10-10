import Mathlib

namespace OAI

                                  
section
namespace UniformKServer.RosterTails

/-- The Taylor cubic suffices for both lifetime tail estimates; retaining an
explicit (loose) absolute constant avoids a separate asymptotic hypothesis. -/
theorem cubic_exp_bound (x : ℝ) (hx : 0 ≤ x) : x^3*Real.exp (-x/2) ≤ 48 := by
  have ht := Real.pow_div_factorial_le_exp (x/2) (by linarith : 0 ≤ x/2) 3
  norm_num at ht
  have hp := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg (-x/2))
  have he : Real.exp (x/2)*Real.exp (-x/2) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [he] at hp
  nlinarith

theorem geometric_exp_bound (q : ℝ) (hq : q ≤ 1) (n : ℕ) :
    (1-q)^n ≤ Real.exp (-(n:ℝ)*q) := by
  have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1-q) (Real.one_sub_le_exp_neg q) n
  rw [←Real.exp_nat_mul] at h
  simpa only [mul_neg,neg_mul] using h

/-- Actual (long) lifetimes: deterministic through age K-1, probability 1/K
at ages K through K²-1, and compulsory retirement at K². -/
theorem actual_tail (K : ℕ) (hK : 2 ≤ K) :
    1/(K:ℝ)+(K:ℝ)^2*(1-1/(K:ℝ))^(K^2-K) ≤ 49/(K:ℝ) := by
  have hk : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hkpos : (0:ℝ) < K := by linarith
  have hkne : (K:ℝ) ≠ 0 := ne_of_gt hkpos
  have hnat : K ≤ K^2 := by nlinarith
  have hq : 1/(K:ℝ) ≤ 1 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hg := geometric_exp_bound (1/(K:ℝ)) hq (K^2-K)
  have hn : ((K^2-K:ℕ):ℝ) = (K:ℝ)^2-K := by
    rw [Nat.cast_sub hnat,Nat.cast_pow]
  rw [hn] at hg
  have hexp : -((K:ℝ)^2-K)*(1/(K:ℝ)) ≤ -(K:ℝ)/2 := by
    field_simp
    nlinarith
  have hgl := hg.trans (Real.exp_le_exp.mpr hexp)
  have hb := cubic_exp_bound (K:ℝ) hkpos.le
  have hm := mul_le_mul_of_nonneg_left hgl (sq_nonneg (K:ℝ))
  have hm' := mul_le_mul_of_nonneg_right hm hkpos.le
  apply (le_div_iff₀ hkpos).mpr
  rw [add_mul,div_mul_cancel₀ _ hkne]
  nlinarith

/-- Auxiliary short lifetimes: probability K^-1/2 at every age increment and
compulsory retirement at K. This is distinct from the actual partition law. -/
theorem short_tail (K : ℕ) (hK : 2 ≤ K) :
    1/Real.sqrt K+(K:ℝ)*(1-1/Real.sqrt K)^(K-1) ≤ 49/Real.sqrt K := by
  have hk : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0:ℝ) ≤ K := by positivity
  have hspos : 0 < Real.sqrt (K:ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsne : Real.sqrt (K:ℝ) ≠ 0 := ne_of_gt hspos
  have hsq := Real.sq_sqrt hk0
  have hs1 : 1 ≤ Real.sqrt (K:ℝ) := (Real.le_sqrt (by norm_num) hk0).mpr (by nlinarith)
  have hq : 1/Real.sqrt (K:ℝ) ≤ 1 := (div_le_iff₀ hspos).mpr (by linarith)
  have hg := geometric_exp_bound (1/Real.sqrt (K:ℝ)) hq (K-1)
  have hn : ((K-1:ℕ):ℝ) = (K:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hn] at hg
  have hexp : -((K:ℝ)-1)*(1/Real.sqrt (K:ℝ)) ≤ -Real.sqrt (K:ℝ)/2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hspos).mpr
    nlinarith
  have hgl := hg.trans (Real.exp_le_exp.mpr hexp)
  have hb := cubic_exp_bound (Real.sqrt (K:ℝ)) hspos.le
  have hm := mul_le_mul_of_nonneg_left hgl hk0
  have hm' := mul_le_mul_of_nonneg_right hm hspos.le
  apply (le_div_iff₀ hspos).mpr
  rw [add_mul,div_mul_cancel₀ _ hsne]
  nlinarith

end UniformKServer.RosterTails

end



end OAI
