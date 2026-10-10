import OAI.NumberTheory.Ostmann.Construction.ExponentialSampling
import OAI.NumberTheory.Ostmann.Preliminaries.SummandSquareComparison

namespace OAI

/-! # A concrete polynomial bootstrap for summand counts

The second sampling length is exponential. Only the integer powers 6, 8 and
12 are needed; a general subpower theorem is unnecessary for this application.
-/

namespace Ostmann

open Filter

 theorem constant_log_linear_small (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ≤ x := by
  have hs := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hs, eventually_ge_atTop (max 1 (2 * C))] with x hx hxl
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hxl
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hh : C * Real.log x ≤ x / 2 := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC hlog), abs_of_nonneg hx0,
      one_div, div_eq_mul_inv, one_mul, mul_comm] using hx
  have hlarge := (le_max_right 1 (2 * C)).trans hxl
  nlinarith

 theorem EventuallyPrimeSumset.summand_polynomial_bootstrap {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∀ᶠ t : ℕ in atTop,
      ((summandPrefix A (t ^ 12)).card : ℝ) ≤ (t : ℝ) ^ 8 := by
  obtain ⟨N₀, hcomp⟩ := h.summand_square_comparison hB.nonempty
  let K : ℝ := N₀ + 8067
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsmall := tendsto_natCast_atTop_atTop.eventually (constant_log_linear_small K hK)
  have htend : Tendsto (fun t : ℕ => t ^ 6) atTop atTop := tendsto_pow_atTop (by norm_num)
  filter_upwards [htend.eventually hcomp, h.exponential_sample_population hB,
    hsmall, eventually_ge_atTop (2 : ℕ)] with t hc hp hs ht
  have htp : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have hlog : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg ht1
  have hlog6 : Real.log (2 * ((t ^ 6 : ℕ) : ℝ)) ≤ 7 * Real.log (t : ℝ) := by
    have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ t by exact_mod_cast ht)
    rw [Nat.cast_pow, Real.log_mul (by norm_num) (pow_pos htp 6).ne', Real.log_pow]
    norm_num
    linarith
  have hfrac : 3 * ((t ^ 6 : ℕ) : ℝ) /
      ((summandPrefix B (exponentialSample t)).card : ℝ) ≤ 1 := by
    have hcard : (0 : ℝ) < (summandPrefix B (exponentialSample t)).card :=
      by exact_mod_cast hp.2.1.card_pos
    apply (div_le_iff₀ hcard).mpr
    simpa only [Nat.cast_pow, one_mul] using hp.2.2
  have hbound := hc (exponentialSample t) hp.1 hp.2.1
  have hlogY := (exponentialSample_log t).2
  have hsum : Real.log (exponentialSample t : ℝ) +
      3 * ((t ^ 6 : ℕ) : ℝ) / ((summandPrefix B (exponentialSample t)).card : ℝ) ≤
        3 * (t : ℝ) := by linarith
  have hsum0 : 0 ≤ Real.log (exponentialSample t : ℝ) +
      3 * ((t ^ 6 : ℕ) : ℝ) / ((summandPrefix B (exponentialSample t)).card : ℝ) := by
    have := (exponentialSample_log t).1
    positivity
  have hmain : 384 * ((t ^ 6 : ℕ) : ℝ) * Real.log (2 * ((t ^ 6 : ℕ) : ℝ)) *
      (Real.log (exponentialSample t : ℝ) +
        3 * ((t ^ 6 : ℕ) : ℝ) / ((summandPrefix B (exponentialSample t)).card : ℝ)) ≤
          8064 * (t : ℝ) ^ 7 * Real.log (t : ℝ) := by
    calc
      _ ≤ 384 * ((t ^ 6 : ℕ) : ℝ) * (7 * Real.log (t : ℝ)) * (3 * (t : ℝ)) := by
        gcongr
      _ = _ := by push_cast; ring
  have ht6 : (1 : ℝ) ≤ (t : ℝ) ^ 6 := one_le_pow₀ ht1
  have ht67 : (t : ℝ) ^ 6 ≤ (t : ℝ) ^ 7 := by
    simpa only [pow_succ] using le_mul_of_one_le_right (pow_nonneg htp.le 6) ht1
  have hboundary : (N₀ : ℝ) + 2 * ((t ^ 6 : ℕ) : ℝ) + 1 ≤ K * (t : ℝ) ^ 7 := by
    have hfirst : (N₀ : ℝ) + 2 * (t : ℝ) ^ 6 + 1 ≤ (N₀ + 3 : ℝ) * (t : ℝ) ^ 6 := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N₀) (sub_nonneg.mpr ht6)]
    push_cast
    calc
      _ ≤ (N₀ + 3 : ℝ) * (t : ℝ) ^ 6 := hfirst
      _ ≤ (N₀ + 3 : ℝ) * (t : ℝ) ^ 7 := mul_le_mul_of_nonneg_left ht67 (by positivity)
      _ ≤ K * (t : ℝ) ^ 7 := by dsimp [K]; gcongr; norm_num
  have hmainK : 8064 * (t : ℝ) ^ 7 * Real.log (t : ℝ) ≤
      K * (t : ℝ) ^ 7 * Real.log (t : ℝ) := by
    dsimp [K]
    gcongr
    have := Nat.cast_nonneg (α := ℝ) N₀
    linarith
  have hfinal : ((summandPrefix A (t ^ 12)).card : ℝ) ≤
      K * (t : ℝ) ^ 7 * (1 + Real.log (t : ℝ)) := by
    have hb : ((summandPrefix A (t ^ 12)).card : ℝ) ≤
        (N₀ : ℝ) + 2 * ((t ^ 6 : ℕ) : ℝ) + 1 +
          8064 * (t : ℝ) ^ 7 * Real.log (t : ℝ) := by
      simpa only [← pow_mul, show (6 : ℕ) * 2 = 12 by norm_num] using
        hbound.trans (add_le_add_right hmain _)
    nlinarith [hboundary, hmainK]
  calc
    _ ≤ K * (t : ℝ) ^ 7 * (1 + Real.log (t : ℝ)) := hfinal
    _ = (t : ℝ) ^ 7 * (K * (1 + Real.log (t : ℝ))) := by ring
    _ ≤ (t : ℝ) ^ 7 * t := mul_le_mul_of_nonneg_left hs (pow_nonneg htp.le 7)
    _ = _ := by ring

end Ostmann

end OAI
