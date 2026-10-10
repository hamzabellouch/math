import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedAsymptotics

namespace OAI

/-! # Resource envelopes including the executed word generators -/

noncomputable section
namespace LowSpaceSubsetSum.WordExecutionAsymptotics

variable {n : ℕ}

theorem counter_limit (I : Instance n) (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000) :
    inputScale I^624*2^((n+1)/2) < 2^n := by
  have hu : (0 : ℝ) < inputScale I := by
    exact_mod_cast (show 0 < inputScale I by unfold inputScale; omega)
  have he : (((n+1)/2 : ℕ) : ℝ) ≤ (1/2 : ℝ)*n+1 := by
    have h : 2*((n+1)/2) ≤ n+1 := by omega
    have h' : (2 : ℝ)*((n+1)/2 : ℕ) ≤ n+1 := by exact_mod_cast h
    linarith only [h']
  have h := guarded_polynomial_exponential hn hu hscale 624
    (a := (1/2 : ℝ)) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he)
    (show 0 ≤ (inputScale I : ℝ)^624 by positivity)
  have hh : ((inputScale I^624*2^((n+1)/2) : ℕ) : ℝ) < (2 : ℝ)^n := by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.rpow_natCast] using hm.trans_lt h
  exact_mod_cast hh

theorem time (c : ℕ) (hc : 0 < c) (n : ℕ) (hn : 2 ≤ n)
    (I : Instance n) (hI : inputBits I ≤ n^c) :
    ((inputScale I^624*2^((n+1)/2) : ℕ) : ℝ) ≤
      ((3 : ℝ)^624*2)*(n : ℝ)^(624*c)*(2 : ℝ)^((1/2 : ℝ)*n) := by
  have hu : (inputScale I : ℝ) ≤ 3*(n : ℝ)^c := by
    exact_mod_cast polynomial_bit_bound hn hc hI
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ inputScale I) hu 624
  have hhalf : (((n+1)/2 : ℕ) : ℝ) ≤ (1/2 : ℝ)*n+1 := by
    have h : 2*((n+1)/2) ≤ n+1 := by omega
    have hh : (2 : ℝ)*((n+1)/2 : ℕ) ≤ n+1 := by exact_mod_cast h
    linarith only [hh]
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hhalf
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (mul_le_mul hp (by simpa only [Real.rpow_natCast] using he)
    (by positivity) (by positivity)).trans
  rw [mul_pow,←pow_mul,Nat.mul_comm c 624,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2),Real.rpow_one]
  exact le_of_eq (by ac_rfl)

end LowSpaceSubsetSum.WordExecutionAsymptotics

end

end OAI
