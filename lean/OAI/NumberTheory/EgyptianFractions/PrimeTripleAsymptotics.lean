import Mathlib

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337

/-- Any fixed logarithmic power is eventually smaller than an arbitrary
positive multiple of a positive real power. -/
lemma eventually_log_pow_lt_mul_rpow (n : ℕ) (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ n < c * x ^ r := by
  have hsmall : (fun x : ℝ => (Real.log x) ^ n) =o[atTop] (fun x : ℝ => x ^ r) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (n : ℝ) hr
  have hlim := hsmall.tendsto_div_nhds_zero
  filter_upwards [hlim.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos hx0 r)).1 hx

/-- The exceptional-prime triple estimate is lower order than the quantitative
three-prime main term. This is purely an asymptotic comparison, not a
three-prime theorem. -/
lemma eventually_exceptional_triples_lt_main_term (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ (7 / 4 : ℝ) * Real.log x * Real.log (Real.log x) <
        c * x ^ (2 : ℕ) / (Real.log x) ^ 3 := by
  have hC1 : 0 < C + 1 := by positivity
  have heps : 0 < c / (C + 1) := div_pos hc hC1
  filter_upwards [eventually_log_pow_lt_mul_rpow 5 (1 / 4) (c / (C + 1))
    (by norm_num) heps, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hp : 0 < x ^ (7 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hloglog : Real.log (Real.log x) ≤ Real.log x := Real.log_le_self hlog.le
  have hsmall : C * (Real.log x) ^ 5 < c * x ^ (1 / 4 : ℝ) := by
    have h := (lt_div_iff₀ hC1).1 (show (Real.log x) ^ 5 <
      (c * x ^ (1 / 4 : ℝ)) / (C + 1) by convert hx using 1; ring)
    nlinarith [show 0 ≤ (Real.log x) ^ 5 by positivity]
  have hpowers : x ^ (7 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (2 : ℕ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  apply (lt_div_iff₀ (pow_pos hlog 3)).2
  calc
    (C * x ^ (7 / 4 : ℝ) * Real.log x * Real.log (Real.log x)) * Real.log x ^ 3 ≤
        x ^ (7 / 4 : ℝ) * (C * Real.log x ^ 5) := by
      nlinarith [mul_le_mul_of_nonneg_left hloglog
        (show 0 ≤ C * x ^ (7 / 4 : ℝ) * Real.log x ^ 4 by positivity)]
    _ < x ^ (7 / 4 : ℝ) * (c * x ^ (1 / 4 : ℝ)) :=
      mul_lt_mul_of_pos_left hsmall hp
    _ = c * x ^ (2 : ℕ) := by rw [← hpowers]; ring

/-- Natural-index form targeting a count of exceptional primes: the elementary
bound `3 * u * B u` for contaminated ordered triples is negligible. -/
lemma eventually_exceptional_prime_triple_count_small (B : ℕ → ℕ) (C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hB : ∀ᶠ u : ℕ in atTop,
      (B u : ℝ) ≤ C * (u : ℝ) ^ (3 / 4 : ℝ) * Real.log (u : ℝ) *
        Real.log (Real.log (u : ℝ))) :
    ∀ᶠ u : ℕ in atTop,
      (3 : ℝ) * (u : ℝ) * (B u : ℝ) <
        c * (u : ℝ) ^ (2 : ℕ) / Real.log (u : ℝ) ^ 3 := by
  have hsmall := (tendsto_natCast_atTop_atTop : Tendsto (fun u : ℕ => (u : ℝ))
    atTop atTop).eventually
    (eventually_exceptional_triples_lt_main_term (3 * C) c (by positivity) hc)
  filter_upwards [hsmall, hB, eventually_gt_atTop (0 : ℕ)] with u hu hBu hu0
  have hx0 : (0 : ℝ) < u := by exact_mod_cast hu0
  have hpowers : (u : ℝ) * (u : ℝ) ^ (3 / 4 : ℝ) = (u : ℝ) ^ (7 / 4 : ℝ) := by
    calc
      (u : ℝ) * (u : ℝ) ^ (3 / 4 : ℝ) =
          (u : ℝ) ^ (1 : ℝ) * (u : ℝ) ^ (3 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = (u : ℝ) ^ (7 / 4 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  calc
    (3 : ℝ) * (u : ℝ) * (B u : ℝ) ≤
        3 * (u : ℝ) * (C * (u : ℝ) ^ (3 / 4 : ℝ) * Real.log (u : ℝ) *
          Real.log (Real.log (u : ℝ))) := mul_le_mul_of_nonneg_left hBu (by positivity)
    _ = (3 * C) * (u : ℝ) ^ (7 / 4 : ℝ) * Real.log (u : ℝ) *
          Real.log (Real.log (u : ℝ)) := by rw [← hpowers]; ring
    _ < c * (u : ℝ) ^ (2 : ℕ) / Real.log (u : ℝ) ^ 3 := hu

end Problem337

end

end OAI
