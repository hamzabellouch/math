import OAI.NumberTheory.EgyptianFractions.RationalSupplyReduction

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeFourier

/-- Exact Fourier extraction of a weighted ordered triple in a finite cyclic
 group. No primality or analytic estimate is needed. -/
theorem weighted_triple_character_identity {q : ℕ} [NeZero q]
    {α : Type*} (s : Finset α) (f : α → ZMod q) (w : α → ℂ)
    (u : ZMod q) :
    (∑ r : ZMod q, (∑ a ∈ s, w a * ZMod.stdAddChar (f a * r)) ^ 3 *
      ZMod.stdAddChar (-u * r)) =
    (q : ℂ) * ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
      if f a + f b + f c = u then w a * w b * w c else 0 := by
  classical
  have hexpand (r : ZMod q) :
      (∑ a ∈ s, w a * ZMod.stdAddChar (f a * r)) ^ 3 *
        ZMod.stdAddChar (-u * r) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
        (w a * w b * w c) * ZMod.stdAddChar ((f a + f b + f c - u) * r) := by
    calc
      _ = ((∑ a ∈ s, w a * ZMod.stdAddChar (f a * r)) *
          (∑ b ∈ s, w b * ZMod.stdAddChar (f b * r)) *
          (∑ c ∈ s, w c * ZMod.stdAddChar (f c * r))) *
          ZMod.stdAddChar (-u * r) := by ring
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        rw [sub_mul, add_mul, add_mul, sub_eq_add_neg,
          AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
        rw [neg_mul]
        ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
        ∑ r : ZMod q,
          (w a * w b * w c) * ZMod.stdAddChar ((f a + f b + f c - u) * r) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [← Finset.mul_sum, FiveProducts.character_sum, sub_eq_zero]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> ring

/-- Choosing the cyclic modulus above every possible sum removes all modular
aliasing. The resulting identity counts ordinary natural-number sums exactly. -/
theorem weighted_natural_triple_character_identity {q : ℕ} [NeZero q]
    (s : Finset ℕ) (w : ℕ → ℂ) (u : ℕ)
    (hs : ∀ a ∈ s, a ≤ u) (hq : 3 * u < q) :
    (∑ r : ZMod q, (∑ a ∈ s, w a * ZMod.stdAddChar ((a : ZMod q) * r)) ^ 3 *
      ZMod.stdAddChar (-(u : ZMod q) * r)) =
    (q : ℂ) * ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
      if a + b + c = u then w a * w b * w c else 0 := by
  classical
  rw [weighted_triple_character_identity]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have habc : a + b + c < q := by
    have := hs a ha
    have := hs b hb
    have := hs c hc
    omega
  have hu : u < q := by omega
  have heq : (a : ZMod q) + (b : ZMod q) + (c : ZMod q) = (u : ZMod q) ↔
      a + b + c = u := by
    rw [← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt habc, Nat.mod_eq_of_lt hu]
  simp only [heq]

/-- Normalized inverse Fourier extraction for weighted ordinary triples. -/
theorem weighted_natural_triple_fourier {q : ℕ} [NeZero q]
    (s : Finset ℕ) (w : ℕ → ℂ) (u : ℕ)
    (hs : ∀ a ∈ s, a ≤ u) (hq : 3 * u < q) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
      if a + b + c = u then w a * w b * w c else 0) =
    (∑ r : ZMod q, (∑ a ∈ s, w a * ZMod.stdAddChar ((a : ZMod q) * r)) ^ 3 *
      ZMod.stdAddChar (-(u : ZMod q) * r)) / (q : ℂ) := by
  apply (eq_div_iff (NeZero.ne (q : ℂ))).2
  simpa only [mul_comm] using
    (weighted_natural_triple_character_identity s w u hs hq).symm

/-- The existing ordered-prime-triple finset is exactly the filtered cube
 of the primes at most `u`. This identity also applies to arbitrary weights. -/
theorem supply_prime_triple_sum_eq_nested (u : ℕ) (w : ℕ → ℂ) :
    (∑ t ∈ supplyPrimeTriples u, w t.1 * w t.2.1 * w t.2.2) =
    ∑ a ∈ (Finset.Icc 1 u).filter Nat.Prime,
      ∑ b ∈ (Finset.Icc 1 u).filter Nat.Prime,
        ∑ c ∈ (Finset.Icc 1 u).filter Nat.Prime,
          if a + b + c = u then w a * w b * w c else 0 := by
  classical
  let s := (Finset.Icc 1 u).filter Nat.Prime
  have hset : ((s ×ˢ (s ×ˢ s)).filter
      (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = u)) =
      supplyPrimeTriples u := by
    ext t
    simp only [s, supplyPrimeTriples, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [← hset]
  simp only [Finset.sum_filter, Finset.sum_product, s]

/-- Exact extraction of the log-weighted prime count that occurs in the
 three-prime lower bound. The modulus condition excludes all circular sums. -/
theorem supply_prime_weighted_fourier {q : ℕ} [NeZero q]
    (u : ℕ) (hq : 3 * u < q) :
    (∑ t ∈ supplyPrimeTriples u,
      (Real.log (t.1 : ℝ) : ℂ) * (Real.log (t.2.1 : ℝ) : ℂ) *
        (Real.log (t.2.2 : ℝ) : ℂ)) =
    (∑ r : ZMod q,
      (∑ a ∈ (Finset.Icc 1 u).filter Nat.Prime,
        (Real.log (a : ℝ) : ℂ) * ZMod.stdAddChar ((a : ZMod q) * r)) ^ 3 *
          ZMod.stdAddChar (-(u : ZMod q) * r)) / (q : ℂ) := by
  rw [supply_prime_triple_sum_eq_nested u (fun a => (Real.log (a : ℝ) : ℂ))]
  apply weighted_natural_triple_fourier _ _ _ _ hq
  intro a ha
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2

/-- Real-part version of the exact extraction formula. -/
theorem supply_prime_weighted_fourier_re {q : ℕ} [NeZero q]
    (u : ℕ) (hq : 3 * u < q) :
    (∑ t ∈ supplyPrimeTriples u,
      Real.log (t.1 : ℝ) * Real.log (t.2.1 : ℝ) * Real.log (t.2.2 : ℝ)) =
    (∑ r : ZMod q,
      (∑ a ∈ (Finset.Icc 1 u).filter Nat.Prime,
        (Real.log (a : ℝ) : ℂ) * ZMod.stdAddChar ((a : ZMod q) * r)) ^ 3 *
          ZMod.stdAddChar (-(u : ZMod q) * r)).re / (q : ℝ) := by
  have h := congrArg Complex.re (supply_prime_weighted_fourier u hq)
  simpa only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re,
    ← Complex.ofReal_natCast, Complex.div_ofReal_re] using h

/-- Splitting frequencies into an arbitrary major set and its complement
 gives the standard lower bound by the major real part minus the minor norm. -/
theorem major_minor_real_lower_bound {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (F : α → ℂ) (Q : ℝ) (hQ : 0 < Q) :
    ((∑ r ∈ s, F r).re - ‖∑ r ∈ sᶜ, F r‖) / Q ≤
      (∑ r, F r).re / Q := by
  classical
  apply div_le_div_of_nonneg_right _ hQ.le
  rw [← Finset.sum_add_sum_compl s F, Complex.add_re]
  have h := Complex.re_le_norm (-(∑ r ∈ sᶜ, F r))
  simp only [Complex.neg_re, norm_neg] at h
  linarith

/-- A lower major-frequency bound and an upper minor-frequency norm bound
 imply a lower bound for the actual log-weighted ordered-prime-triple count.
 The genuinely analytic estimates remain explicit hypotheses. -/
theorem supply_prime_weighted_lower_of_major_minor {q : ℕ} [NeZero q]
    (u : ℕ) (hq : 3 * u < q) (major : Finset (ZMod q))
    (A E : ℝ)
    (hmajor : A * (q : ℝ) ≤
      (∑ r ∈ major,
        (∑ a ∈ (Finset.Icc 1 u).filter Nat.Prime,
          (Real.log (a : ℝ) : ℂ) * ZMod.stdAddChar ((a : ZMod q) * r)) ^ 3 *
            ZMod.stdAddChar (-(u : ZMod q) * r)).re)
    (hminor : ‖∑ r ∈ majorᶜ,
        (∑ a ∈ (Finset.Icc 1 u).filter Nat.Prime,
          (Real.log (a : ℝ) : ℂ) * ZMod.stdAddChar ((a : ZMod q) * r)) ^ 3 *
            ZMod.stdAddChar (-(u : ZMod q) * r)‖ ≤ E * (q : ℝ)) :
    A - E ≤ ∑ t ∈ supplyPrimeTriples u,
      Real.log (t.1 : ℝ) * Real.log (t.2.1 : ℝ) * Real.log (t.2.2 : ℝ) := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [supply_prime_weighted_fourier_re u hq]
  let F : ZMod q → ℂ := fun r =>
    (∑ a ∈ (Finset.Icc 1 u).filter Nat.Prime,
      (Real.log (a : ℝ) : ℂ) * ZMod.stdAddChar ((a : ZMod q) * r)) ^ 3 *
        ZMod.stdAddChar (-(u : ZMod q) * r)
  change A - E ≤ (∑ r, F r).re / (q : ℝ)
  have hsplit := major_minor_real_lower_bound major F (q : ℝ) hqpos
  refine le_trans ?_ hsplit
  apply (le_div_iff₀ hqpos).2
  change A * (q : ℝ) ≤ (∑ r ∈ major, F r).re at hmajor
  change ‖∑ r ∈ majorᶜ, F r‖ ≤ E * (q : ℝ) at hminor
  nlinarith

end Problem337.ThreePrimeFourier

end

end OAI
