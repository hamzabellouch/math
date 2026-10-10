import OAI.NumberTheory.DukePrimeDegree.Geometry.AdjacentFirstRoot

namespace OAI

/-! # Neutral weights for every lexicographic elimination step

The least remaining root can be kept neutral while all other remaining
root directions contract. Thus the actual Gaussian elimination order
has the weights needed by the conditional product induction.
-/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def lexicographicNeutralRaw {n : ℕ} (a b i : Fin n) : ℝ :=
  if i = a then (b.val : ℝ) else (i.val : ℝ)

lemma lexicographicNeutralRaw_equal {n : ℕ} {a b : Fin n} (hab : a < b) :
    lexicographicNeutralRaw a b a = lexicographicNeutralRaw a b b := by
  simp [lexicographicNeutralRaw, ne_of_gt hab]

lemma lexicographicNeutralRaw_strict {n : ℕ}
    (S : Finset (Fin n × Fin n)) {a b : Fin n}
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hmin : ∀ p ∈ S, toLex (a,b) ≤ toLex p)
    (p : Fin n × Fin n) (hp : p ∈ S) (hne : p ≠ (a,b)) :
    lexicographicNeutralRaw a b p.1 < lexicographicNeutralRaw a b p.2 := by
  have har : a ≤ p.1 := by
    by_contra h
    exact not_lt_of_ge (hmin p hp)
      (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (lt_of_not_ge h)))
  have hca : p.2 ≠ a := by
    intro h
    have hlt : p.1 < a := by simpa only [h] using hpos p hp
    exact not_lt_of_ge har hlt
  by_cases hra : p.1 = a
  · have hbc : b < p.2 := by
      have hle : b ≤ p.2 := by
        by_contra h
        exact not_lt_of_ge (hmin p hp)
          (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hra, lt_of_not_ge h⟩))
      refine lt_of_le_of_ne hle ?_
      intro h
      exact hne (Prod.ext hra h.symm)
    simpa only [lexicographicNeutralRaw, ite_eq_left hra, ite_eq_right hca] using
      (show (b.val : ℝ) < p.2.val by exact_mod_cast hbc)
  · simpa only [lexicographicNeutralRaw, ite_eq_right hra, ite_eq_right hca] using
      (show (p.1.val : ℝ) < p.2.val by exact_mod_cast hpos p hp)

theorem exists_lexicographic_root_weights (d : ℕ)
    (S : Finset (Fin (d + 1) × Fin (d + 1))) {a b : Fin (d + 1)}
    (hab : a < b) (hpos : ∀ p ∈ S, p.1 < p.2)
    (hmin : ∀ p ∈ S, toLex (a,b) ≤ toLex p) :
    ∃ ell : Fin (d + 1) → ℝ, (∑ i, ell i) = 0 ∧ ell a = ell b ∧
      ∀ p ∈ S, p ≠ (a,b) → ell p.1 < ell p.2 := by
  refine ⟨centerWeights d (lexicographicNeutralRaw a b), centerWeights_sum _ _, ?_, ?_⟩
  · unfold centerWeights
    rw [lexicographicNeutralRaw_equal hab]
  · intro p hp hne
    apply sub_neg.mp
    rw [centerWeights_sub]
    exact sub_neg.mpr (lexicographicNeutralRaw_strict S hpos hmin p hp hne)

lemma initialRemaining_roots_closed {n : ℕ}
    (P : Finset (Fin n × Fin n)) (hP : InitialRootPattern P) :
    ∀ a b c : Fin n, (a,b) ∈ allPositiveRoots n \ P →
      (b,c) ∈ allPositiveRoots n \ P → (a,c) ∈ allPositiveRoots n \ P := by
  intro a b c hab hbc
  obtain ⟨hab, habP⟩ := Finset.mem_sdiff.mp hab
  obtain ⟨hbc, _⟩ := Finset.mem_sdiff.mp hbc
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_trans (Finset.mem_filter.mp hab).2 (Finset.mem_filter.mp hbc).2⟩
  · intro hacP
    exact habP ((hP (a,c) hacP).2 (a,b) hab
      (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, (Finset.mem_filter.mp hbc).2⟩)))

lemma initialRemaining_erase {n : ℕ} (P : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    (allPositiveRoots n \ P).erase p = allPositiveRoots n \ insert p P := by
  ext q
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
  tauto

end DukePrimeDegree

end

end OAI
