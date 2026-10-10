import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
namespace Ostmann.Construction

private theorem positive_pow_eq_exp (z : ℝ) (hz : 0<z) (n : ℕ) :
    z^n=Real.exp ((n:ℝ)*Real.log z) := by
  conv_lhs => rw [←Real.exp_log hz]
  rw [Real.exp_nat_mul]

theorem diagonal_factorial_harmonic_gain (r m : ℕ) (L z : ℝ)
    (hL : 0<L) (hz : 0<z) (hmz : (m:ℝ)/L≤z) :
    ((m.factorial:ℝ)^r)/L^(r*m)≤Real.exp ((r:ℝ)*m*Real.log z) := by
  have hf : (m.factorial:ℝ)≤(m:ℝ)^m := by exact_mod_cast Nat.factorial_le_pow m
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg m.factorial) hf r
  have hratio : ((m.factorial:ℝ)^r)/L^(r*m)≤((m:ℝ)/L)^(r*m) := by
    calc
      _ ≤ ((m:ℝ)^m)^r/L^(r*m) := div_le_div_of_nonneg_right hpow (pow_nonneg hL.le _)
      _ = (m:ℝ)^(r*m)/L^(r*m) := by rw [←pow_mul,Nat.mul_comm m r]
      _ = _ := by rw [div_pow]
  refine hratio.trans ((pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hL.le) hmz _).trans_eq ?_)
  rw [positive_pow_eq_exp z hz]
  congr 1
  push_cast
  ring

theorem diagonal_full_factorial_harmonic_gain (r m : ℕ) (L z : ℝ)
    (hr : 0<r) (hL : 0<L) (hz : 0<z) (hmz : (m:ℝ)/L≤z) :
    (((r*m).factorial:ℝ))/L^(r*m)≤Real.exp ((r:ℝ)*m*Real.log ((r:ℝ)*z)) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hratio : ((r*m:ℕ):ℝ)/L≤(r:ℝ)*z := by
    push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hmz hrR.le
  simpa only [pow_one,Nat.cast_one,one_mul,Nat.one_mul,Nat.cast_mul] using
    diagonal_factorial_harmonic_gain 1 (r*m) L ((r:ℝ)*z) hL (mul_pos hrR hz) hratio

theorem selected_bulk_ratio_le (k : ℕ) (L : ℝ) (hL : 0<L) :
    (Conclusion.bulkSize k L:ℝ)/L≤Conclusion.bulkScale k := by
  apply (div_le_iff₀ hL).mpr
  exact (Conclusion.bulkSize_bounds k hL.le).2

end Ostmann.Construction

end

end OAI
