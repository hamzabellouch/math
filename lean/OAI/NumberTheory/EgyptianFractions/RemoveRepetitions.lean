import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Replacing two equal unit fractions by two unequal smaller-first terms. -/
theorem reciprocal_pair_replacement (m : ℕ) (hm : 3 ≤ m) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a < m ∧
      (1 : ℚ) / a + 1 / b = 1 / m + 1 / m := by
  rcases Nat.even_or_odd m with he | ho
  · rcases he with ⟨p, rfl⟩
    have hp : 2 ≤ p := by omega
    refine ⟨p + 1, p * (p + 1), by omega, by nlinarith, by omega, ?_⟩
    have hp0 : (p : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  · rcases ho with ⟨p, rfl⟩
    have hp : 1 ≤ p := by omega
    refine ⟨p + 1, (p + 1) * (2 * p + 1), by omega, by nlinarith, by omega, ?_⟩
    push_cast
    field_simp
    ring

/-- Effect of a one-coordinate replacement on a finite reciprocal sum. -/
theorem reciprocal_sum_update {k : ℕ} (n : Fin k → ℕ) (i : Fin k) (a : ℕ) :
    (∑ t, (1 : ℚ) / (Function.update n i a t : ℚ)) =
      (∑ t, (1 : ℚ) / (n t : ℚ)) + 1 / (a : ℚ) - 1 / (n i : ℚ) := by
  classical
  simp_rw [Function.apply_update (fun _ (v : ℕ) => (1 : ℚ) / v)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  ring

/-- Two-coordinate replacement preserves the sum when the two reciprocals agree. -/
theorem reciprocal_sum_update_two {k : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i ≠ j) (a b : ℕ)
    (hab : (1 : ℚ) / a + 1 / b = 1 / n i + 1 / n j) :
    (∑ t, (1 : ℚ) / (Function.update (Function.update n i a) j b t : ℚ)) =
      ∑ t, (1 : ℚ) / (n t : ℚ) := by
  rw [reciprocal_sum_update, reciprocal_sum_update]
  simp only [Function.update_of_ne hij.symm]
  linarith

/-- Any first-coordinate decrease beats a later-coordinate change lexicographically. -/
theorem lex_update_two_lt {k : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i < j) (a b : ℕ) (ha : a < n i) :
    Pi.Lex (· < ·) (· < ·) (Function.update (Function.update n i a) j b) n := by
  refine ⟨i, ?_, ?_⟩
  · intro t ht
    simp [Function.update_of_ne (ne_of_lt ht), Function.update_of_ne (ne_of_lt (ht.trans hij))]
  · simpa [Function.update_of_ne (ne_of_lt hij)] using ha

/-- A reusable lexicographic minimization principle for constrained tuples. -/
theorem exists_strictMono_of_two_replacements {k : ℕ}
    (P : (Fin k → ℕ) → Prop) (hP : ∃ n, P n)
    (hstep : ∀ n, P n → ∀ i j : Fin k, i < j → n j ≤ n i →
      ∃ a b : ℕ, a < n i ∧ P (Function.update (Function.update n i a) j b)) :
    ∃ n, P n ∧ StrictMono n := by
  have hwf : WellFounded (Pi.Lex (· < ·) (fun {i : Fin k} (a b : ℕ) => a < b)) :=
    Pi.Lex.wellFounded (· < ·)
  obtain ⟨n, hn, hminimal⟩ := hwf.has_min {n | P n} hP
  refine ⟨n, hn, ?_⟩
  intro i j hij
  by_contra! hnot
  obtain ⟨a, b, halt, hab⟩ := hstep n hn i j hij hnot
  exact hminimal _ hab (lex_update_two_lt n hij a b halt)

/-- Takenouchi cleanup, proved using a lexicographically least tuple.
No distinctness or ordering is required of the original representation. -/
theorem remove_repetitions_below_one {k : ℕ} (x : ℚ)
    (hx : x < 1) (original : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ original i)
    (hsum : (∑ i, (1 : ℚ) / (original i : ℚ)) = x) :
    ∃ n : Fin k → ℕ, (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
      (∑ i, (1 : ℚ) / (n i : ℚ)) = x := by
  classical
  let S : Set (Fin k → ℕ) :=
    {n | (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = x}
  have hwf : WellFounded (Pi.Lex (· < ·) (fun {i : Fin k} (a b : ℕ) => a < b)) :=
    Pi.Lex.wellFounded (· < ·)
  obtain ⟨n, hn, hminimal⟩ := hwf.has_min S ⟨original, hpos, hsum⟩
  change (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = x at hn
  have hreplace (i j : Fin k) (hij : i < j) (a b : ℕ)
      (ha : 1 ≤ a) (hb : 1 ≤ b) (halt : a < n i)
      (hab : (1 : ℚ) / a + 1 / b = 1 / n i + 1 / n j) : False := by
    apply hminimal (Function.update (Function.update n i a) j b) ?_
      (lex_update_two_lt n hij a b halt)
    constructor
    · intro t
      by_cases htj : t = j
      · subst t
        simpa using hb
      · by_cases hti : t = i
        · subst t
          simpa [Function.update_of_ne htj] using ha
        · simpa [Function.update_of_ne htj, Function.update_of_ne hti] using hn.1 t
    · rw [reciprocal_sum_update_two n hij.ne a b hab]
      exact hn.2
  have hsingle (i : Fin k) : (1 : ℚ) / n i ≤ x := by
    calc
      (1 : ℚ) / n i ≤ ∑ t : Fin k, (1 : ℚ) / n t := by
        exact Finset.single_le_sum (f := fun t : Fin k => (1 : ℚ) / n t) (fun t _ => by positivity) (Finset.mem_univ i)
      _ = x := hn.2
  have htwo : ∀ i, 2 ≤ n i := by
    intro i
    have hi := hn.1 i
    by_contra! h
    have heq : n i = 1 := by omega
    have := hsingle i
    norm_num [heq] at this
    linarith
  refine ⟨n, htwo, ?_, hn.2⟩
  intro i j hij
  by_contra! hnot
  rcases lt_or_eq_of_le hnot with hlt | heq
  · exact hreplace i j hij (n j) (n i) (hn.1 j) (hn.1 i) hlt (add_comm _ _)
  · have hpair : (1 : ℚ) / n i + 1 / n j ≤ x := by
      calc
        (1 : ℚ) / n i + 1 / n j = ∑ t ∈ ({i, j} : Finset (Fin k)), (1 : ℚ) / n t :=
          (Finset.sum_pair (f := fun t : Fin k => (1 : ℚ) / n t) hij.ne).symm
        _ ≤ ∑ t : Fin k, (1 : ℚ) / n t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = x := hn.2
    have hm : 3 ≤ n i := by
      have hi := htwo i
      by_contra! h
      have heq2 : n i = 2 := by omega
      rw [heq, heq2] at hpair
      norm_num at hpair
      linarith
    obtain ⟨a, b, ha, hb, halt, hab⟩ := reciprocal_pair_replacement (n i) hm
    exact hreplace i j hij a b ha hb halt (by simpa [heq] using hab)

end Problem337

end

end OAI
