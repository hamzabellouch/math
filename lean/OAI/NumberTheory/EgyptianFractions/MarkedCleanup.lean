import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.RemoveRepetitions

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Takenouchi's duplicate replacement preserves every odd divisor of the repeated denominator. -/
theorem marked_duplicate_replacement (m : ℕ) (hm : 3 ≤ m) :
    ∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧ u < m ∧
      2 * m < u + v ∧
      (2 : ℚ) / (m : ℚ) = 1 / (u : ℚ) + 1 / (v : ℚ) ∧
      (∀ Q : ℕ, Odd Q → Q ∣ m → Q ∣ v) := by
  rcases Nat.even_or_odd m with heven | hodd
  · obtain ⟨p, rfl⟩ := heven
    have hp : 2 ≤ p := by omega
    refine ⟨p + 1, p * (p + 1), by omega, by nlinarith, by omega, ?_, ?_, ?_⟩
    · nlinarith [Nat.mul_le_mul_left p hp]
    · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · intro Q hQ hdiv
      have hdiv' : Q ∣ 2 * p := by simpa [two_mul] using hdiv
      have hpdiv : Q ∣ p := hQ.coprime_two_right.dvd_of_dvd_mul_left hdiv'
      exact dvd_mul_of_dvd_left hpdiv (p + 1)
  · obtain ⟨p, rfl⟩ := hodd
    have hp : 1 ≤ p := by omega
    refine ⟨p + 1, (p + 1) * (2 * p + 1), by omega, by nlinarith, by omega, ?_, ?_, ?_⟩
    · nlinarith [Nat.mul_le_mul_left p hp]
    · have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      have hp2 : 2 * (p : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · intro Q _ hdiv
      exact dvd_mul_of_dvd_right hdiv (p + 1)

/-- An odd marker greater than one forces its denominator to be at least three. -/
theorem odd_marker_denominator_ge_three {Q n : ℕ} (hQ : Odd Q)
    (hQone : 1 < Q) (hn : 0 < n) (hdiv : Q ∣ n) : 3 ≤ n := by
  have hQthree : 3 ≤ Q := by
    obtain ⟨p, hp⟩ := hQ
    omega
  exact hQthree.trans (Nat.le_of_dvd hn hdiv)

/-- A positive expansion of one carrying an odd marker cannot have denominator one. -/
theorem marked_sum_one_denominators_ge_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = 1)
    {Q : ℕ} (hQ : Odd Q) (hQone : 1 < Q) (hmarker : ∃ i, Q ∣ n i) :
    ∀ i, 2 ≤ n i := by
  obtain ⟨j, hj⟩ := hmarker
  have hjthree : 3 ≤ n j := odd_marker_denominator_ge_three hQ hQone (hn j) hj
  intro i
  by_contra hni
  have hione : n i = 1 := by have := hn i; omega
  have hji : j ≠ i := by intro h; subst j; omega
  have hlt : (1 : ℚ) / (n i : ℚ) < ∑ k, (1 : ℚ) / (n k : ℚ) := by
    apply Finset.single_lt_sum hji (Finset.mem_univ i) (Finset.mem_univ j)
    · exact one_div_pos.mpr (by exact_mod_cast hn j)
    · intro k _ _
      exact le_of_lt (one_div_pos.mpr (by exact_mod_cast hn k))
  rw [hione, hsum] at hlt
  norm_num at hlt

/-- In a marked expansion of one, any repeated denominator is at least three. -/
theorem marked_sum_one_duplicate_ge_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = 1)
    {Q : ℕ} (hQ : Odd Q) (hQone : 1 < Q) (hmarker : ∃ i, Q ∣ n i)
    {i j : ι} (hij : i ≠ j) (heq : n i = n j) : 3 ≤ n i := by
  have htwo := marked_sum_one_denominators_ge_two n hn hsum hQ hQone hmarker i
  by_contra hthree
  have hitwo : n i = 2 := by omega
  have hjtwo : n j = 2 := by omega
  obtain ⟨k, hk⟩ := hmarker
  have hkthree := odd_marker_denominator_ge_three hQ hQone (hn k) hk
  have hki : k ≠ i := by intro h; subst k; omega
  have hkj : k ≠ j := by intro h; subst k; omega
  have hlt : (∑ l ∈ ({i, j} : Finset ι), (1 : ℚ) / (n l : ℚ)) <
      ∑ l, (1 : ℚ) / (n l : ℚ) := by
    apply Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ k)
      (by simp [hki, hkj])
    · exact one_div_pos.mpr (by exact_mod_cast hn k)
    · intro l _ _
      exact le_of_lt (one_div_pos.mpr (by exact_mod_cast hn l))
  rw [Finset.sum_pair hij, hitwo, hjtwo, hsum] at hlt
  norm_num at hlt

/-- A two-coordinate update retains an odd-divisibility marker whenever removed markers are restored. -/
theorem marker_update_two {k Q : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i ≠ j) (a b : ℕ) (hmarker : ∃ t, Q ∣ n t)
    (hrestore : Q ∣ n i ∨ Q ∣ n j → Q ∣ a ∨ Q ∣ b) :
    ∃ t, Q ∣ Function.update (Function.update n i a) j b t := by
  obtain ⟨t, ht⟩ := hmarker
  by_cases hti : t = i
  · subst t
    rcases hrestore (Or.inl ht) with ha | hb
    · exact ⟨i, by simpa [Function.update_of_ne hij] using ha⟩
    · exact ⟨j, by simpa using hb⟩
  · by_cases htj : t = j
    · subst t
      rcases hrestore (Or.inr ht) with ha | hb
      · exact ⟨i, by simpa [Function.update_of_ne hij] using ha⟩
      · exact ⟨j, by simpa using hb⟩
    · exact ⟨t, by simpa [Function.update_of_ne htj, Function.update_of_ne hti] using ht⟩

/-- Exact-length cleanup at total one, retaining a denominator divisible by a specified odd integer. -/
theorem marked_cleanup_exact_length {k Q : ℕ} (hQ : Odd Q) (hQone : 1 < Q)
    (original : Fin k → ℕ) (hpos : ∀ i, 1 ≤ original i)
    (hsum : (∑ i, (1 : ℚ) / (original i : ℚ)) = 1)
    (hmarker : ∃ i, Q ∣ original i) :
    ∃ n : Fin k → ℕ, IsOneExpansion n ∧ ∃ i, Q ∣ n i := by
  classical
  let S : Set (Fin k → ℕ) :=
    {n | (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = 1 ∧ ∃ i, Q ∣ n i}
  have hwf : WellFounded (Pi.Lex (· < ·) (fun {i : Fin k} (a b : ℕ) => a < b)) :=
    Pi.Lex.wellFounded (· < ·)
  obtain ⟨n, hn, hminimal⟩ := hwf.has_min S ⟨original, hpos, hsum, hmarker⟩
  change (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = 1 ∧ (∃ i, Q ∣ n i) at hn
  have hreplace (i j : Fin k) (hij : i < j) (a b : ℕ)
      (ha : 1 ≤ a) (hb : 1 ≤ b) (halt : a < n i)
      (hab : (1 : ℚ) / a + 1 / b = 1 / n i + 1 / n j)
      (hrestore : Q ∣ n i ∨ Q ∣ n j → Q ∣ a ∨ Q ∣ b) : False := by
    apply hminimal (Function.update (Function.update n i a) j b) ?_
      (lex_update_two_lt n hij a b halt)
    refine ⟨?_, ?_, marker_update_two n hij.ne a b hn.2.2 hrestore⟩
    · intro t
      by_cases htj : t = j
      · subst t; simpa using hb
      · by_cases hti : t = i
        · subst t; simpa [Function.update_of_ne htj] using ha
        · simpa [Function.update_of_ne htj, Function.update_of_ne hti] using hn.1 t
    · rw [reciprocal_sum_update_two n hij.ne a b hab]
      exact hn.2.1
  refine ⟨n, ⟨hn.1, ?_, hn.2.1⟩, hn.2.2⟩
  intro i j hij
  by_contra! hnot
  rcases lt_or_eq_of_le hnot with hlt | heq
  · exact hreplace i j hij (n j) (n i) (hn.1 j) (hn.1 i) hlt
      (add_comm _ _) (fun h => h.elim Or.inr Or.inl)
  · have hm : 3 ≤ n i := marked_sum_one_duplicate_ge_three n hn.1 hn.2.1
      hQ hQone hn.2.2 hij.ne heq.symm
    obtain ⟨a, b, ha, hb, halt, _, hab, hdiv⟩ := marked_duplicate_replacement (n i) hm
    apply hreplace i j hij a b ha hb halt
    · rw [heq]
      calc
        (1 : ℚ) / a + 1 / b = 2 / (n i : ℚ) := hab.symm
        _ = 1 / (n i : ℚ) + 1 / (n i : ℚ) := by ring
    · intro h
      apply Or.inr
      apply hdiv Q hQ
      rcases h with hi | hj
      · exact hi
      · simpa [heq] using hj

/-- The at-most-length formulation used in the counting construction. -/
theorem marked_cleanup {k Q : ℕ} (hQ : Odd Q) (hQone : 1 < Q)
    (original : Fin k → ℕ) (hpos : ∀ i, 1 ≤ original i)
    (hsum : (∑ i, (1 : ℚ) / (original i : ℚ)) = 1)
    (hmarker : ∃ i, Q ∣ original i) :
    ∃ r : ℕ, r ≤ k ∧ ∃ n : Fin r → ℕ, IsOneExpansion n ∧ ∃ i, Q ∣ n i := by
  obtain ⟨n, hn, hm⟩ := marked_cleanup_exact_length hQ hQone original hpos hsum hmarker
  exact ⟨k, le_rfl, n, hn, hm⟩

end Problem337

end

end OAI
