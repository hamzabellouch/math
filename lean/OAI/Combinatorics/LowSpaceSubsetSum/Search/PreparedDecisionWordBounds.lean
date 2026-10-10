import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedDecision

namespace OAI

/-! # The repeated execution counter fits the fixed machine word -/

namespace LowSpaceSubsetSum.PreparedDecisionWordBounds

variable {n : ℕ}

theorem counter_limit (I : Instance n) (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000) :
    inputScale I ^ 622 * 2 ^ ((n+1)/2) < 2 ^ n := by
  have hu : (0 : ℝ) < inputScale I := by
    exact_mod_cast (show 0 < inputScale I by unfold inputScale; omega)
  have he : (((n+1)/2 : ℕ) : ℝ) ≤ (1/2 : ℝ)*n+1 := by
    have h : 2*((n+1)/2) ≤ n+1 := by omega
    have h' : (2 : ℝ)*((n+1)/2 : ℕ) ≤ n+1 := by exact_mod_cast h
    linarith only [h']
  have hh := guarded_polynomial_exponential hn hu hscale 622
    (a := (1/2 : ℝ)) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he)
    (show 0 ≤ (inputScale I : ℝ)^622 by positivity)
  have hc : ((inputScale I ^ 622 * 2 ^ ((n+1)/2) : ℕ) : ℝ) < (2 : ℝ)^n := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using hm.trans_lt hh
  exact_mod_cast hc

theorem work_fits (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (s : PreparedDecision.Seed I hn) :
    (PreparedDecision.run I hn hscale s).2 < 2 ^ wordWidth I :=
  cutoff_fits_word I ((PreparedDecision.work I hn hscale s).trans_lt
    (counter_limit I (by omega) hscale))

end LowSpaceSubsetSum.PreparedDecisionWordBounds

end OAI
