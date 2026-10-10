import Mathlib

namespace OAI
noncomputable section

open Filter

namespace Problem337

private theorem marked_loglog_tendsto :
    Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Convert the supply's size budget into the short grouping budget. -/
theorem marked_group_budget (K G : ℕ → ℝ)
    (hK : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      Real.log (K m) ≤ (32 / Real.log 2 + δ) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hG : ∀ᶠ m : ℕ in atTop,
      G m ≤ (Real.log (K m) + Real.log (2 * (m : ℝ))) /
        (2 * Real.log (m : ℝ)) + 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      G m ≤ (16 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  intro ε hε
  have hlarge : ∀ᶠ m : ℕ in atTop, 6 / ε ≤ Real.log (Real.log (m : ℝ)) :=
    marked_loglog_tendsto.eventually (eventually_ge_atTop (6 / ε))
  filter_upwards [hK ε hε, hG, hlarge, eventually_ge_atTop (2 : ℕ)] with m hK hG hlarge hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hlog2m : Real.log (2 * (m : ℝ)) ≤ 2 * Real.log (m : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
    linarith
  have hG' : (G m - 2) * (2 * Real.log (m : ℝ)) ≤
      Real.log (K m) + Real.log (2 * (m : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log (m : ℝ))).1
    linarith
  have hproduct : (2 * G m) * Real.log (m : ℝ) ≤
      ((32 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) + 6) *
        Real.log (m : ℝ) := by nlinarith
  have hsimple := le_of_mul_le_mul_right hproduct hlogm
  have hlarge' : 6 ≤ Real.log (Real.log (m : ℝ)) * ε :=
    (div_le_iff₀ hε).1 hlarge
  have hcoef : (32 : ℝ) / Real.log 2 = 2 * (16 / Real.log 2) := by ring
  nlinarith

/-- Elementary error absorption used after taking a second logarithm. -/
theorem eventually_log_add_const_le_mul (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x + C ≤ ε * x := by
  have htlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have htconst : Tendsto (fun x : ℝ => C / x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto (fun x : ℝ => (Real.log x + C) / x) atTop (nhds 0) := by
    simpa [add_div] using htlog.add htconst
  filter_upwards [ht.eventually_le_const hε, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  exact (div_le_iff₀ hxpos).1 hx

/-- Convert the greedy stopping-time formula and supply size into the prefix
coefficient.  A fixed coarse supply bound suffices for this part. -/
theorem marked_prefix_budget (K J : ℕ → ℝ)
    (hKpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ K m)
    (hK : ∀ᶠ m : ℕ in atTop,
      Real.log (K m) ≤ (32 / Real.log 2 + 1) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hJ : ∀ᶠ m : ℕ in atTop,
      J m ≤ 3 + (Real.log (Real.log (2 * (m : ℝ) * K m)) -
        Real.log (Real.log 2)) / Real.log 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      J m ≤ (1 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := 32 / Real.log 2 + 3
  let C : ℝ := Real.log B - Real.log (Real.log 2) + 3 * Real.log 2
  have hB : 0 < B := by dsimp [B]; positivity
  have herror : ∀ᶠ m : ℕ in atTop,
      Real.log (Real.log (Real.log (m : ℝ))) + C ≤
        (ε * Real.log 2) * Real.log (Real.log (m : ℝ)) :=
    marked_loglog_tendsto.eventually
      (eventually_log_add_const_le_mul C (ε * Real.log 2) (mul_pos hε hlog2))
  have hlarge : ∀ᶠ m : ℕ in atTop, 1 ≤ Real.log (Real.log (m : ℝ)) :=
    marked_loglog_tendsto.eventually (eventually_ge_atTop 1)
  filter_upwards [hKpositive, hK, hJ, herror, hlarge, eventually_ge_atTop (2 : ℕ)]
    with m hKpositive hK hJ herror hlarge hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hL : 0 < Real.log (Real.log (m : ℝ)) := by linarith
  have hT : 1 < 2 * (m : ℝ) * K m := by nlinarith
  have hlogT : Real.log (2 * (m : ℝ) * K m) ≤
      B * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    have hlog2le := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
    dsimp [B]
    nlinarith
  have hloglogT : Real.log (Real.log (2 * (m : ℝ) * K m)) ≤
      Real.log (Real.log (m : ℝ)) + Real.log (Real.log (Real.log (m : ℝ))) +
        Real.log B := by
    calc
      Real.log (Real.log (2 * (m : ℝ) * K m)) ≤
          Real.log (B * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))) :=
        Real.log_le_log (Real.log_pos hT) hlogT
      _ = _ := by
        rw [Real.log_mul (by positivity) (ne_of_gt hL),
          Real.log_mul (ne_of_gt hB) (ne_of_gt hlogm)]
        ring
  have hJ' : (J m - 3) * Real.log 2 ≤
      Real.log (Real.log (2 * (m : ℝ) * K m)) - Real.log (Real.log 2) := by
    apply (le_div_iff₀ hlog2).1
    linarith
  apply le_of_mul_le_mul_right (a := Real.log 2) ?_ hlog2
  have hident : ((1 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ))) * Real.log 2 =
      Real.log (Real.log (m : ℝ)) + (ε * Real.log 2) * Real.log (Real.log (m : ℝ)) := by
    field_simp
  rw [hident]
  dsimp [C] at herror
  linarith

end Problem337

end

end OAI
