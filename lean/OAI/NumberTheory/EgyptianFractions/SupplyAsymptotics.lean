import Mathlib

namespace OAI
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace Problem337

/-- The logarithms lost in the exceptional-prime count are absorbed by any
positive power of the main parameter. -/
theorem supply_log_factor_isLittleO (δ : ℝ) (hδ : 0 < δ) :
    (fun x : ℝ => Real.log x ^ 4 * Real.log (Real.log x)) =o[atTop]
      (fun x : ℝ => x ^ δ) := by
  have hmajor :
      (fun x : ℝ => Real.log x ^ 4 * Real.log (Real.log x)) =O[atTop]
        (fun x : ℝ => Real.log x ^ 5) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    have hx0 : 0 ≤ Real.log x := le_trans (by norm_num) hx
    have hloglog : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hx
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx0 4) hloglog)]
    calc
      Real.log x ^ 4 * Real.log (Real.log x) ≤
          Real.log x ^ 4 * Real.log x :=
        mul_le_mul_of_nonneg_left (Real.log_le_self hx0) (pow_nonneg hx0 4)
      _ = Real.log x ^ 5 := by ring
  apply hmajor.trans_isLittleO
  simpa only [Real.rpow_ofNat] using
    (isLittleO_log_rpow_rpow_atTop (5 : ℝ) hδ)

/-- Exceptional prime triples in the rational-divisor supply have lower order
than the quantitative three-prime main term. This is only the analytic
comparison; no three-prime theorem is assumed or asserted here. -/
theorem supply_exceptional_triples_isLittleO :
    (fun x : ℝ => x ^ (7 / 4 : ℝ) * Real.log x * Real.log (Real.log x))
      =o[atTop] (fun x : ℝ => x ^ 2 / Real.log x ^ 3) := by
  have hsmall := supply_log_factor_isLittleO (1 / 4) (by norm_num)
  have hscaled := hsmall.mul_isBigO
    (isBigO_refl (fun x : ℝ => x ^ (7 / 4 : ℝ) / Real.log x ^ 3) atTop)
  apply hscaled.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [← mul_div_assoc, ← Real.rpow_add (by linarith : 0 < x)]
    norm_num

/-- Any fixed multiple of the exceptional count is eventually smaller than
any positive fixed multiple of the main term. -/
theorem supply_exceptional_triples_eventually_lt (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      C * (x ^ (7 / 4 : ℝ) * Real.log x * Real.log (Real.log x)) <
        c * (x ^ 2 / Real.log x ^ 3) := by
  have hsmall := supply_exceptional_triples_isLittleO.const_mul_left C
  have he := hsmall.bound (show 0 < c / 2 by positivity)
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hmain : 0 < x ^ 2 / Real.log x ^ 3 := by positivity
  have hnorm : ‖x ^ 2 / Real.log x ^ 3‖ = x ^ 2 / Real.log x ^ 3 :=
    Real.norm_of_nonneg hmain.le
  rw [hnorm] at hx
  exact lt_of_le_of_lt (le_trans (le_abs_self _) hx) (by nlinarith)

/-- Direct natural-parameter form of the estimate used to discard triples
containing one of the exceptional primes. -/
theorem supply_bad_triples_eventually_lt (B : ℕ → ℝ) (C c : ℝ) (hc : 0 < c)
    (hB : ∀ᶠ n : ℕ in atTop,
      B n ≤ C * ((n : ℝ) ^ (3 / 4 : ℝ) * Real.log n * Real.log (Real.log n))) :
    ∀ᶠ n : ℕ in atTop,
      3 * (n : ℝ) * B n < c * ((n : ℝ) ^ 2 / Real.log n ^ 3) := by
  have he := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (supply_exceptional_triples_eventually_lt (3 * C) c hc)
  filter_upwards [hB, he, eventually_ge_atTop 1] with n hn he hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (n : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) ^ (7 / 4 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnpos]
    norm_num
  calc
    3 * (n : ℝ) * B n ≤
        3 * (n : ℝ) * (C * ((n : ℝ) ^ (3 / 4 : ℝ) *
          Real.log n * Real.log (Real.log n))) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (3 * C) * ((n : ℝ) ^ (7 / 4 : ℝ) *
          Real.log n * Real.log (Real.log n)) := by rw [← hp]; ring
    _ < c * ((n : ℝ) ^ 2 / Real.log n ^ 3) := he

end Problem337

end

end OAI
