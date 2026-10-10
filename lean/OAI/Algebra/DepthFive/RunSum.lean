import OAI.Algebra.DepthFive.WordRuns

namespace OAI

/-! Quantitative run-weight sums for the path-type estimate. -/

open scoped BigOperators

namespace Problem335.RunSum

/-- The inequality form also includes the constant all-true word. -/
theorem switches_card_le_two_interior_add_two {n : ℕ} (w : Fin (n + 1) → Bool) :
    (WordSwitches.switches w).card ≤ 2 * WordRuns.interiorRunCount w + 2 := by
  rw [WordRuns.switches_card_eq_rises_add_falls]
  have h := WordRuns.rise_first_eq_fall_last w
  unfold WordRuns.interiorRunCount WordRuns.runCount WordRuns.endpointRunCount
  cases hfirst : w 0 <;> cases hlast : w (Fin.last n) <;> simp_all <;> omega

/-- A pointwise switch-weight bound gives an exponential bound after summing all words. -/
theorem sum_le_exp_of_switch_bound (n : ℕ) (q A : ℝ) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (F : (Fin (n + 1) → Bool) → ℝ)
    (hF : ∀ w, F w ≤ A * q ^ (WordSwitches.switches w).card) :
    (∑ w, F w) ≤ 2 * A * Real.exp ((n : ℝ) * q) := by
  calc
    (∑ w, F w) ≤ ∑ w, A * q ^ (WordSwitches.switches w).card :=
      Finset.sum_le_sum (fun w _ => hF w)
    _ = A * ∑ w, q ^ (WordSwitches.switches w).card := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (2 * Real.exp ((n : ℝ) * q)) :=
      mul_le_mul_of_nonneg_left (WordSwitches.sum_pow_switches_le_exp n q hq) hA
    _ = 2 * A * Real.exp ((n : ℝ) * q) := by ring

/-- The sum of the interior-run weights is controlled by the switch generating function. -/
theorem sum_pow_two_interiorRuns_le (n : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    (∑ w : Fin (n + 1) → Bool, q ^ (2 * WordRuns.interiorRunCount w)) ≤
      2 * (q ^ 2)⁻¹ * Real.exp ((n : ℝ) * q) := by
  apply sum_le_exp_of_switch_bound n q ((q ^ 2)⁻¹) hq.le (by positivity)
  intro w
  calc
    q ^ (2 * WordRuns.interiorRunCount w) =
        (q ^ 2)⁻¹ * q ^ (2 * WordRuns.interiorRunCount w + 2) := by
      rw [pow_add]
      field_simp
    _ ≤ (q ^ 2)⁻¹ * q ^ (WordSwitches.switches w).card := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one hq.le hq1 (switches_card_le_two_interior_add_two w)

/-- A convenient quantitative form of the run-count estimate in the path-word argument. -/
theorem sum_inv_pow_interiorRuns_le (n : ℕ) :
    (∑ w : Fin (n + 1) → Bool, (((n + 1 : ℕ) : ℝ)⁻¹) ^ WordRuns.interiorRunCount w) ≤
      2 * ((n + 1 : ℕ) : ℝ) * Real.exp (Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hs1 : 1 ≤ Real.sqrt N := by
    exact (Real.le_sqrt (by norm_num) hN.le).mpr (by simpa using hN1)
  have hq : 0 < (Real.sqrt N)⁻¹ := inv_pos.mpr hs
  have hq1 : (Real.sqrt N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hq2 : ((Real.sqrt N)⁻¹) ^ 2 = N⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hN.le]
  have hpow (w : Fin (n + 1) → Bool) :
      ((Real.sqrt N)⁻¹) ^ (2 * WordRuns.interiorRunCount w) = N⁻¹ ^ WordRuns.interiorRunCount w := by
    rw [pow_mul, hq2]
  have h := sum_pow_two_interiorRuns_le n ((Real.sqrt N)⁻¹) hq hq1
  simp_rw [hpow, hq2, inv_inv] at h
  have hexponent : (n : ℝ) * (Real.sqrt N)⁻¹ ≤ Real.sqrt N := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hs).mpr
    have hsq := Real.sq_sqrt hN.le
    have hnN : (n : ℝ) + 1 = N := by simp [N]
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity))

/-- Absorb the polynomial factor in the elementary run estimate into a square-root exponential. -/
theorem two_mul_self_mul_exp_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    2 * x * Real.exp (Real.sqrt x) ≤ Real.exp (4 * Real.sqrt x) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hs1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by simpa using hx)
  have hs0 := Real.sqrt_nonneg x
  have h2 : 2 ≤ Real.exp (Real.sqrt x) := by linarith [Real.add_one_le_exp (Real.sqrt x)]
  have hs : Real.sqrt x ≤ Real.exp (Real.sqrt x) := by linarith [Real.add_one_le_exp (Real.sqrt x)]
  have hxx : x ≤ Real.exp (2 * Real.sqrt x) := by
    calc
      x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx0).symm
      _ ≤ Real.exp (Real.sqrt x) ^ 2 := pow_le_pow_left₀ hs0 hs 2
      _ = Real.exp (2 * Real.sqrt x) := by simpa using (Real.exp_nat_mul (Real.sqrt x) 2).symm
  calc
    2 * x * Real.exp (Real.sqrt x) ≤
        Real.exp (Real.sqrt x) * Real.exp (2 * Real.sqrt x) * Real.exp (Real.sqrt x) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul h2 hxx hx0 (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (4 * Real.sqrt x) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The full run-weight sum is at most `exp (4 sqrt(length))`, with an explicit absolute constant. -/
theorem sum_inv_pow_interiorRuns_le_exp (n : ℕ) :
    (∑ w : Fin (n + 1) → Bool, (((n + 1 : ℕ) : ℝ)⁻¹) ^ WordRuns.interiorRunCount w) ≤
      Real.exp (4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  exact (sum_inv_pow_interiorRuns_le n).trans
    (two_mul_self_mul_exp_sqrt_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)))

/-- Application form: any pointwise run-weight estimate can be summed with the same absolute loss. -/
theorem sum_le_exp_of_interiorRun_bound (n : ℕ) (C : ℝ)
    (F : (Fin (n + 1) → Bool) → ℝ)
    (hF : ∀ w, F w ≤ Real.exp C * (((n + 1 : ℕ) : ℝ)⁻¹) ^ WordRuns.interiorRunCount w) :
    (∑ w, F w) ≤ Real.exp (C + 4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  calc
    (∑ w, F w) ≤ ∑ w, Real.exp C * (((n + 1 : ℕ) : ℝ)⁻¹) ^ WordRuns.interiorRunCount w :=
      Finset.sum_le_sum (fun w _ => hF w)
    _ = Real.exp C * ∑ w, (((n + 1 : ℕ) : ℝ)⁻¹) ^ WordRuns.interiorRunCount w :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp C * Real.exp (4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inv_pow_interiorRuns_le_exp n) (Real.exp_nonneg C)
    _ = Real.exp (C + 4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := (Real.exp_add _ _).symm


/-- Counting both endpoint bits (including twice for a constant true run) gives an exact balance. -/
theorem switches_card_add_endpoint_eq_two_runs {n : ℕ} (w : Fin (n + 1) → Bool) :
    (WordSwitches.switches w).card + WordRuns.endpointRunCount w =
      2 * WordRuns.runCount w := by
  rw [WordRuns.switches_card_eq_rises_add_falls]
  have h := WordRuns.rise_first_eq_fall_last w
  unfold WordRuns.runCount WordRuns.endpointRunCount
  omega

/-- Switch penalties pay for all but at most one square scale of the run weights.
The constant words are included, so no exceptional-case partition is needed. -/
theorem switch_penalty_mul_run_weight_le {n : ℕ} (w : Fin (n + 1) → Bool)
    {N : ℝ} (hN : 1 ≤ N) :
    N⁻¹ ^ (WordSwitches.switches w).card * N ^ WordRuns.runCount w ≤
      N * (Real.sqrt N)⁻¹ ^ (WordSwitches.switches w).card := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hs1 : 1 ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) hN0.le).mpr (by simpa using hN)
  have he := switches_card_add_endpoint_eq_two_runs w
  have he2 := WordRuns.endpointRunCount_le_two w
  have hr : 2 * WordRuns.runCount w ≤ (WordSwitches.switches w).card + 2 := by omega
  have hpow : N ^ WordRuns.runCount w ≤
      Real.sqrt N ^ ((WordSwitches.switches w).card + 2) := by
    calc
      N ^ WordRuns.runCount w = Real.sqrt N ^ (2 * WordRuns.runCount w) := by
        rw [pow_mul, Real.sq_sqrt hN0.le]
      _ ≤ _ := pow_le_pow_right₀ hs1 hr
  calc
    N⁻¹ ^ (WordSwitches.switches w).card * N ^ WordRuns.runCount w ≤
        N⁻¹ ^ (WordSwitches.switches w).card *
          Real.sqrt N ^ ((WordSwitches.switches w).card + 2) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = N * (Real.sqrt N)⁻¹ ^ (WordSwitches.switches w).card := by
      rw [pow_add, Real.sq_sqrt hN0.le]
      have hNinv : N⁻¹ = (Real.sqrt N)⁻¹ ^ 2 := by rw [inv_pow, Real.sq_sqrt hN0.le]
      rw [hNinv, ← pow_mul, Nat.mul_comm 2 _, pow_mul]
      simp only [inv_pow]
      field_simp

/-- Direct application to products of interval weights: a factor `N` per true run,
with `N⁻¹` per switch, yields the required square-root exponential sum. -/
theorem sum_switch_penalty_mul_run_weight_le_exp (n : ℕ) :
    (∑ w : Fin (n + 1) → Bool,
      (((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
        ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) ≤
      Real.exp (4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsum := sum_le_exp_of_switch_bound n ((Real.sqrt N)⁻¹) N (by positivity) hN0.le
    (fun w => N⁻¹ ^ (WordSwitches.switches w).card * N ^ WordRuns.runCount w)
    (fun w => switch_penalty_mul_run_weight_le w hN)
  have hexponent : (n : ℝ) * (Real.sqrt N)⁻¹ ≤ Real.sqrt N := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hs0).mpr
    have hsq := Real.sq_sqrt hN0.le
    have hnN : (n : ℝ) + 1 = N := by simp [N]
    nlinarith
  exact hsum.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
    (by positivity)).trans (two_mul_self_mul_exp_sqrt_le hN))

/-- Summation interface requiring only a pointwise product-of-runs bound. -/
theorem sum_weighted_switch_penalty_le_exp (n : ℕ) (C : ℝ)
    (F : (Fin (n + 1) → Bool) → ℝ)
    (hF : ∀ w, F w ≤ Real.exp C * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :
    (∑ w, (((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card * F w) ≤
      Real.exp (C + 4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  calc
    _ ≤ ∑ w, Real.exp C * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
        ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) := by
      apply Finset.sum_le_sum
      intro w _
      calc
        _ ≤ (((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
            (Real.exp C * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :=
          mul_le_mul_of_nonneg_left (hF w) (by positivity)
        _ = _ := by ring
    _ = Real.exp C * ∑ w, ((((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
        ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp C * Real.exp (4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_switch_penalty_mul_run_weight_le_exp n) (Real.exp_nonneg C)
    _ = _ := (Real.exp_add _ _).symm

end Problem335.RunSum

end OAI
