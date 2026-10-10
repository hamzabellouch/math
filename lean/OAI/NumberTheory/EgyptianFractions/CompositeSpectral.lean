import OAI.NumberTheory.EgyptianFractions.FiveProducts

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- Ordered tuples with a prescribed sum in a finite cyclic group. -/
def sumTuples {q : ℕ} [NeZero q] {X : Type*} [Fintype X]
    (f : X → ZMod q) (k : ℕ) (t : ZMod q) : Finset (Fin k → X) := by
  classical
  exact Finset.univ.filter (fun v => ∑ i, f (v i) = t)

/-- Exact Fourier inversion for an arbitrary tuple length and target. The
modulus need not be prime, and the sample type can retain multiplicities. -/
theorem sumTuples_fourier {q : ℕ} [NeZero q] {X : Type*} [Fintype X]
    (f : X → ZMod q) (k : ℕ) (t : ZMod q) :
    (∑ r : ZMod q, ZMod.stdAddChar (-t * r) *
      (∑ x : X, ZMod.stdAddChar (f x * r)) ^ k) =
      (q : ℂ) * (sumTuples f k t).card := by
  classical
  simp_rw [Fintype.sum_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (v : Fin k → X) (r : ZMod q) :
      ZMod.stdAddChar (-t * r) *
        (∏ i : Fin k, ZMod.stdAddChar (f (v i) * r)) =
        ZMod.stdAddChar (((∑ i : Fin k, f (v i)) - t) * r) := by
    rw [← FiveProducts.character_map_sum, ← AddChar.map_add_eq_mul]
    congr 1
    rw [← Finset.sum_mul]
    ring
  simp_rw [hterm, FiveProducts.character_sum, sub_eq_zero]
  rw [← Finset.sum_filter]
  simp [sumTuples, mul_comm]

/-- The nontrivial Fourier frequencies control the discrepancy from the
uniform tuple count. Keeping the sum, rather than using a worst frequency,
allows different proper quotients of a composite modulus to be estimated
separately. -/
theorem sumTuples_discrepancy_le {q : ℕ} [NeZero q]
    {X : Type*} [Fintype X] (f : X → ZMod q) (k : ℕ) (t : ZMod q) :
    |(q : ℝ) * (sumTuples f k t).card - (Fintype.card X : ℝ) ^ k| ≤
      ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ^ k := by
  classical
  let S : ZMod q → ℂ := fun r => ZMod.stdAddChar (-t * r) *
    (∑ x : X, ZMod.stdAddChar (f x * r)) ^ k
  have hzero : S 0 = (Fintype.card X : ℂ) ^ k := by simp [S]
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
    S (Finset.mem_univ 0)
  have htotal : ∑ r, S r = (q : ℂ) * (sumTuples f k t).card :=
    sumTuples_fourier f k t
  rw [hzero, htotal] at hsplit
  have hdiff : (q : ℂ) * (sumTuples f k t).card - (Fintype.card X : ℂ) ^ k =
      ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, S r := by
    linear_combination -hsplit
  have hnorm := norm_sum_le ((Finset.univ : Finset (ZMod q)).erase 0) S
  rw [← hdiff] at hnorm
  have hterm (r : ZMod q) : ‖S r‖ =
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ^ k := by
    dsimp [S]
    have hc : ‖ZMod.stdAddChar (-t * r)‖ = 1 := Circle.norm_coe _
    rw [norm_mul, hc, one_mul, norm_pow]
  simp_rw [hterm] at hnorm
  exact_mod_cast hnorm

/-- A frequency-by-frequency bound gives a quantitative lower bound for
the number of tuples having any prescribed sum. -/
theorem sumTuples_lower_bound {q : ℕ} [NeZero q]
    {X : Type*} [Fintype X] (f : X → ZMod q) (k : ℕ) (t : ZMod q)
    (B : ZMod q → ℝ)
    (hB : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ≤ B r) :
    (Fintype.card X : ℝ) ^ k -
      (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ k) ≤
        (q : ℝ) * (sumTuples f k t).card := by
  classical
  have hdisc := sumTuples_discrepancy_le f k t
  have hsum : (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ^ k) ≤
      ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ k := by
    apply Finset.sum_le_sum
    intro r hr
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hB r (Finset.mem_erase.mp hr).1) k
  linarith [(abs_le.mp hdisc).1]

/-- Summed spectral losses below the zero frequency force a tuple of the
specified sum, without any prime-modulus hypothesis. -/
theorem exists_sum_of_character_bounds {q : ℕ} [NeZero q]
    {X : Type*} [Fintype X] (f : X → ZMod q) (k : ℕ) (t : ZMod q)
    (B : ZMod q → ℝ)
    (hB : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ≤ B r)
    (hbudget : (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ k) <
      (Fintype.card X : ℝ) ^ k) :
    ∃ v : Fin k → X, ∑ i, f (v i) = t := by
  classical
  have hcount := sumTuples_lower_bound f k t B hB
  have hpos : 0 < (sumTuples f k t).card := by
    by_contra hn
    have hz : (sumTuples f k t).card = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, Nat.cast_zero, mul_zero] at hcount
    linarith
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  exact ⟨v, (Finset.mem_filter.mp hv).2⟩

/-- Product sums inherit the frequency-dependent criterion. This is the
composite-modulus counterpart of the prime-field five-product extraction;
the genuinely arithmetic spectral budget remains an explicit premise. -/
theorem products_sum_of_character_bounds {q : ℕ} [NeZero q]
    (H : Finset (ZMod q)) (k : ℕ) (t : ZMod q) (B : ZMod q → ℝ)
    (hB : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ a ∈ H, ∑ b ∈ H, ZMod.stdAddChar (a * b * r)‖ ≤ B r)
    (hbudget : (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ k) <
      (H.card : ℝ) ^ (2 * k)) :
    ∃ a b : Fin k → H, ∑ i, (a i : ZMod q) * (b i : ZMod q) = t := by
  classical
  have hpair (r : ZMod q) :
      (∑ z : H × H, ZMod.stdAddChar ((z.1 : ZMod q) * (z.2 : ZMod q) * r)) =
        ∑ a ∈ H, ∑ b ∈ H, ZMod.stdAddChar (a * b * r) := by
    rw [Fintype.sum_prod_type]
    have hi (a : ZMod q) :
        (∑ b : H, ZMod.stdAddChar (a * (b : ZMod q) * r)) =
          ∑ b ∈ H, ZMod.stdAddChar (a * b * r) :=
      Finset.sum_coe_sort H (fun b : ZMod q => ZMod.stdAddChar (a * b * r))
    simp_rw [hi]
    exact Finset.sum_coe_sort H
      (fun a : ZMod q => ∑ b ∈ H, ZMod.stdAddChar (a * b * r))
  have hsize : (Fintype.card (H × H) : ℝ) ^ k = (H.card : ℝ) ^ (2 * k) := by
    simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul]
    rw [pow_mul, pow_two]
  obtain ⟨v, hv⟩ := exists_sum_of_character_bounds
    (fun z : H × H => (z.1 : ZMod q) * (z.2 : ZMod q)) k t B
    (fun r hr => by simpa only [hpair] using hB r hr)
    (by simpa only [hsize] using hbudget)
  exact ⟨fun i => (v i).1, fun i => (v i).2, hv⟩

end Problem337.CompositeSpectral

end

end OAI
