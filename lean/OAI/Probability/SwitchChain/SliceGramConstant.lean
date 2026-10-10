import OAI.Probability.SwitchChain.SliceCoefficientAlgebra
import OAI.Probability.SwitchChain.SliceGramScalars

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem constantPair_meetingSum (c : ℝ) {i j : V} (hij : i ≠ j) :
    meetingSum (constantPair c) i j = 2 * ((Fintype.card V : ℝ) - 2) * c := by
  rw [meetingSum_eq _ (constantPair_symmetric c) (constantPair_diag c) hij,
    constantPair_rowSum, constantPair_rowSum]
  simp only [constantPair, hij, ite_false]
  ring

theorem constantPair_disjointSum (c : ℝ) {i j : V} (hij : i ≠ j) :
    disjointSum (constantPair c) i j =
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * c := by
  unfold disjointSum
  rw [double_outside_eq _ (constantPair_symmetric c) (constantPair_diag c) hij]
  simp only [constantPair_rowSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    constantPair, hij, ite_false]
  ring

theorem intersectionAction_constantPair (a b d c : ℝ) (i j : V) :
    intersectionAction a b d (constantPair c) i j =
      (a + 2 * ((Fintype.card V : ℝ) - 2) * b +
        (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d) *
      constantPair c i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction]
  · simp only [intersectionAction, hij, ite_false,
      constantPair_meetingSum c hij, constantPair_disjointSum c hij,
      constantPair]
    ring

theorem constant_relation_of_intersectionAction_eq_zero [Nontrivial V] (b d : ℝ)
    (hzero : ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0) :
    1 + 2 * ((Fintype.card V : ℝ) - 2) * b +
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  have h := hzero i j
  rw [intersectionAction_constantPair] at h
  simpa [constantPair, hij] using h

theorem degree_two_bound_of_intersectionAction_eq_zero [Nontrivial V]
    (hcard : 4 ≤ Fintype.card V) (b d : ℝ)
    (hzero : ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0)
    (hpositive : 0 ≤ 1 + ((Fintype.card V : ℝ) - 4) * b -
      ((Fintype.card V : ℝ) - 3) * d) :
    1 - 2 * b + d ≤ (Fintype.card V : ℝ) - 1 := by
  apply Problem315.SliceGram.degree_two_eigenvalue_le_johnson
    (Fintype.card V : ℝ) b d
    (1 + ((Fintype.card V : ℝ) - 4) * b - ((Fintype.card V : ℝ) - 3) * d)
    (1 - 2 * b + d) (by exact_mod_cast hcard)
    (constant_relation_of_intersectionAction_eq_zero b d hzero) rfl rfl hpositive

end Problem315.SliceCoefficients

end

end OAI
