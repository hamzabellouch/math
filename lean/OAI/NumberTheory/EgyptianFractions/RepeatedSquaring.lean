import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Iterated squaring after a starting bound. The finite horizon avoids hypotheses
on states beyond the stopping point of an algorithm. -/
theorem repeated_squaring_bound (x : ℕ → ℝ) (a : ℝ) (N : ℕ)
    (_ha : 0 ≤ a) (hzero : x 0 ≤ a)
    (hpos : ∀ i ≤ N, 0 ≤ x i)
    (hstep : ∀ i < N, x (i + 1) ≤ (x i) ^ 2) :
    ∀ i ≤ N, x i ≤ a ^ (2 ^ i) := by
  intro i hi
  induction i with
  | zero => simpa using hzero
  | succ i ih =>
    have hiN : i < N := by omega
    calc
      x (i + 1) ≤ (x i) ^ 2 := hstep i hiN
      _ ≤ (a ^ (2 ^ i)) ^ 2 := by
        exact pow_le_pow_left₀ (hpos i (by omega)) (ih (by omega)) 2
      _ = a ^ (2 ^ (i + 1)) := by rw [← pow_mul, pow_succ]

/-- One exceptional step is permitted to decrease the sequence without squaring it.
After n steps, at least n-1 effective squarings remain. -/
theorem repeated_squaring_one_exception (x : ℕ → ℝ) (t N : ℕ)
    (hzero : x 0 ≤ (1 / 2 : ℝ))
    (hpos : ∀ i ≤ N, 0 ≤ x i)
    (hstep : ∀ i < N, i ≠ t → x (i + 1) ≤ (x i) ^ 2)
    (hexception : t < N → x (t + 1) ≤ x t) :
    ∀ i ≤ N, 1 ≤ i → x i ≤ (1 / 2 : ℝ) ^ (2 ^ (i - 1)) := by
  have hbefore : ∀ i ≤ t, i ≤ N → x i ≤ (1 / 2 : ℝ) ^ (2 ^ i) := by
    intro i hit hiN
    apply repeated_squaring_bound x (1 / 2) i (by norm_num) hzero
      (fun j hj => hpos j (by omega)) ?_ i le_rfl
    intro j hj
    exact hstep j (by omega) (by omega)
  intro i hiN hi
  by_cases hit : i ≤ t
  · have hh := hbefore i hit hiN
    exact hh.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le i 1)))
  · have hti : t < i := by omega
    have htN : t < N := by omega
    have hinit : x (t + 1) ≤ (1 / 2 : ℝ) ^ (2 ^ t) :=
      (hexception htN).trans (hbefore t le_rfl (by omega))
    have htail := repeated_squaring_bound
      (fun j => x (t + 1 + j)) ((1 / 2 : ℝ) ^ (2 ^ t)) (i - (t + 1))
      (by positivity) (by simpa using hinit)
      (by intro j hj; apply hpos; omega)
      (by
        intro j hj
        simpa only [Nat.add_assoc] using
          hstep (t + 1 + j) (by omega) (by omega))
      (i - (t + 1)) le_rfl
    have hi_eq : t + 1 + (i - (t + 1)) = i := by omega
    rw [hi_eq, ← pow_mul, ← pow_add] at htail
    have hexp : t + (i - (t + 1)) = i - 1 := by omega
    simpa only [hexp] using htail

/-- Convert a small positive rational remainder to a large unreduced denominator.
The premise `1 ≤ q*x` expresses that its numerator is a positive integer. -/
theorem denominator_bound_of_small_remainder {x q : ℝ} (e : ℕ)
    (hq : 0 ≤ q) (hnum : 1 ≤ q * x)
    (hx : x ≤ (1 / 2 : ℝ) ^ e) :
    (2 : ℝ) ^ e ≤ q := by
  have hmul : 1 ≤ q * ((1 / 2 : ℝ) ^ e) :=
    hnum.trans (mul_le_mul_of_nonneg_left hx hq)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  rw [one_div_pow] at hmul
  have hdiv : 1 ≤ q / (2 : ℝ) ^ e := by simpa only [div_eq_mul_inv, one_div, one_mul] using hmul
  simpa using (le_div_iff₀ hpow).mp hdiv

/-- Inverting a double power, in the precise base-two convention used by the
marked greedy prefix bound. -/
theorem double_power_lt_loglog_bound (n : ℕ) (T : ℝ)
    (hbound : (2 : ℝ) ^ (2 ^ n) < T) :
    (n : ℝ) < Real.log (Real.log T / Real.log 2) / Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfirst := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n)) hbound
  rw [Real.log_pow] at hfirst
  have hpow : (2 : ℝ) ^ n < Real.log T / Real.log 2 := by
    apply (lt_div_iff₀ hlog2).2
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hfirst
  have hsecond := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ n) hpow
  rw [Real.log_pow] at hsecond
  exact (lt_div_iff₀ hlog2).2 hsecond

/-- The stopping-time estimate for a prefix whose penultimate denominator is below T. -/
theorem marked_prefix_length_of_double_power (j : ℕ) (T : ℝ)
    (hj : 3 ≤ j) (hbound : (2 : ℝ) ^ (2 ^ (j - 3)) < T) :
    (j : ℝ) < 3 + Real.log (Real.log T / Real.log 2) / Real.log 2 := by
  have h := double_power_lt_loglog_bound (j - 3) T hbound
  have hcast : (j : ℝ) = (j - 3 : ℕ) + 3 := by
    exact_mod_cast (show j = j - 3 + 3 by omega)
  linarith

/-- Rational-valued version, convenient for unreduced greedy remainders. -/
theorem repeated_squaring_one_exception_rat (x : ℕ → ℚ) (t N : ℕ)
    (hzero : x 0 ≤ (1 / 2 : ℚ))
    (hpos : ∀ i ≤ N, 0 ≤ x i)
    (hstep : ∀ i < N, i ≠ t → x (i + 1) ≤ (x i) ^ 2)
    (hexception : t < N → x (t + 1) ≤ x t) :
    ∀ i ≤ N, 1 ≤ i → x i ≤ (1 / 2 : ℚ) ^ (2 ^ (i - 1)) := by
  have h := repeated_squaring_one_exception (fun i => (x i : ℝ)) t N
    (by
      have hh : (x 0 : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hzero
      norm_num at hh ⊢
      exact hh)
    (by intro i hi; exact_mod_cast hpos i hi)
    (by intro i hi hit; exact_mod_cast hstep i hi hit)
    (by intro ht; exact_mod_cast hexception ht)
  intro i hi hip
  apply Rat.cast_le (K := ℝ) |>.mp
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h i hi hip

/-- Natural denominator version of the reciprocal remainder estimate. -/
theorem nat_denominator_bound_of_small_remainder (R q e : ℕ)
    (hR : 0 < R) (hq : 0 < q)
    (hsmall : (R : ℚ) / (q : ℚ) ≤ (1 / 2 : ℚ) ^ e) :
    2 ^ e ≤ q := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hnum : (1 : ℝ) ≤ (q : ℝ) * ((R : ℝ) / (q : ℝ)) := by
    rw [mul_div_cancel₀ _ hqR]
    exact_mod_cast hR
  have h := denominator_bound_of_small_remainder e (by positivity) hnum
    (by
      have hh := (Rat.cast_le (K := ℝ)).mpr hsmall
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast, Rat.cast_one,
        Rat.cast_ofNat] using hh)
  exact_mod_cast h

/-- Direct interface for a marked greedy chain, indexed as in the manuscript.
The exceptional transition is t; taking t beyond the horizon covers no exception. -/
theorem marked_greedy_chain_length_bound (R q : ℕ → ℕ) (j t T : ℕ)
    (hj : 3 ≤ j) (ht : 1 ≤ t)
    (hfirst : (R 1 : ℚ) / (q 1 : ℚ) ≤ (1 / 2 : ℚ))
    (hstep : ∀ i, 1 ≤ i → i < j - 1 → i ≠ t →
      (R (i + 1) : ℚ) / (q (i + 1) : ℚ) ≤ ((R i : ℚ) / (q i : ℚ)) ^ 2)
    (hexception : t < j - 1 →
      (R (t + 1) : ℚ) / (q (t + 1) : ℚ) ≤ (R t : ℚ) / (q t : ℚ))
    (hR : 0 < R (j - 1)) (hq : 0 < q (j - 1)) (hactive : q (j - 1) < T) :
    (j : ℝ) < 3 + Real.log (Real.log (T : ℝ) / Real.log 2) / Real.log 2 := by
  let x : ℕ → ℚ := fun i => (R (i + 1) : ℚ) / (q (i + 1) : ℚ)
  have hdecay := repeated_squaring_one_exception_rat x (t - 1) (j - 2)
    hfirst (by intro i hi; dsimp [x]; positivity)
    (by
      intro i hi hit
      exact hstep (i + 1) (by omega) (by omega) (by omega))
    (by
      intro htt
      have ht_eq : t - 1 + 1 = t := by omega
      simpa only [x, ht_eq] using hexception (by omega))
    (j - 2) le_rfl (by omega)
  have heq : j - 2 + 1 = j - 1 := by omega
  have heq2 : j - 2 - 1 = j - 3 := by omega
  have hsmall : (R (j - 1) : ℚ) / (q (j - 1) : ℚ) ≤
      (1 / 2 : ℚ) ^ (2 ^ (j - 3)) := by
    simpa only [x, heq, heq2] using hdecay
  have hden := nat_denominator_bound_of_small_remainder
    (R (j - 1)) (q (j - 1)) (2 ^ (j - 3)) hR hq hsmall
  apply marked_prefix_length_of_double_power j (T : ℝ) hj
  exact_mod_cast hden.trans_lt hactive

/-- A form requiring only uniqueness of a transition which fails to square;
there is no need to choose its index in the construction. -/
theorem repeated_squaring_at_most_one_exception_rat (x : ℕ → ℚ) (N : ℕ)
    (hzero : x 0 ≤ (1 / 2 : ℚ))
    (hpos : ∀ i ≤ N, 0 ≤ x i)
    (hdecrease : ∀ i < N, x (i + 1) ≤ x i)
    (hunique : ∀ i < N, ∀ j < N,
      ¬ x (i + 1) ≤ (x i) ^ 2 → ¬ x (j + 1) ≤ (x j) ^ 2 → i = j) :
    ∀ i ≤ N, 1 ≤ i → x i ≤ (1 / 2 : ℚ) ^ (2 ^ (i - 1)) := by
  by_cases hbad : ∃ t, t < N ∧ ¬ x (t + 1) ≤ (x t) ^ 2
  · obtain ⟨t, ht, hbad⟩ := hbad
    apply repeated_squaring_one_exception_rat x t N hzero hpos
    · intro i hi hit
      by_contra hnot
      exact hit (hunique i hi t ht hnot hbad)
    · intro _
      exact hdecrease t ht
  · apply repeated_squaring_one_exception_rat x N N hzero hpos
    · intro i hi _
      by_contra hnot
      exact hbad ⟨i, hi, hnot⟩
    · omega

/-- Denominator square bound at an integer cut-off; no real rounding is involved. -/
theorem greedy_denominator_below_square (q n T : ℕ)
    (hq : q < T) (hn : n ≤ q + 1) : q * n < T ^ 2 := by
  have hT : 0 < T := by omega
  calc
    q * n ≤ q * (q + 1) := Nat.mul_le_mul_left q hn
    _ ≤ q * T := Nat.mul_le_mul_left q (by omega)
    _ < T * T := Nat.mul_lt_mul_of_pos_right hq hT
    _ = T ^ 2 := by ring

end Problem337

end

end OAI
