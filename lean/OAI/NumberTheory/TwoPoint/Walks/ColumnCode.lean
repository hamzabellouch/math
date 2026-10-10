import OAI.NumberTheory.TwoPoint.Walks.ForestCode

namespace OAI

/-!
# Counting the finite column-code universe

The shape is a typed plane forest on at most `N` vertices. Binary marks
record boundaries and run types. Omitted runs and imperfect positions
store representative indices; regular segments store their two endpoints.
-/

namespace TwoPointCorrelations

instance boundedForestFinite (N : ℕ) : Finite {t : BinaryTree Bool // t.numNodes ≤ N} :=
  Finite.of_injective (boundedForestCode N) (boundedForestCode_injective N)

noncomputable instance boundedForestFintype (N : ℕ) :
    Fintype {t : BinaryTree Bool // t.numNodes ≤ N} := Fintype.ofFinite _

/-- Fixed-size slots can be padded once the nonempty index universe is fixed. -/
abbrev ColumnCode (N segments omitted imperfect : ℕ) :=
  {t : BinaryTree Bool // t.numNodes ≤ N} ×
  (Fin (2 * N) → Bool) × (Fin segments → Fin N × Fin N) ×
  (Fin omitted → Fin N) × (Fin imperfect → Fin N)

/-- The code count is uniform over every numerical realization. -/
theorem card_columnCode_le (N segments omitted imperfect : ℕ) :
    Fintype.card (ColumnCode N segments omitted imperfect) ≤
      2 ^ (5 * N + 1) * N ^ (2 * segments + omitted + imperfect) := by
  have hshape : Fintype.card {t : BinaryTree Bool // t.numNodes ≤ N} ≤ 2 ^ (3 * N + 1) := by
    simpa only [Nat.card_eq_fintype_card] using card_bounded_forests N
  simp only [ColumnCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  calc
    _ ≤ 2 ^ (3 * N + 1) *
        (2 ^ (2 * N) * ((N * N) ^ segments * (N ^ omitted * N ^ imperfect))) := by
      exact Nat.mul_le_mul_right _ hshape
    _ = _ := by
      rw [mul_pow]
      simp only [← pow_add]
      ring_nf

/-- A decoder makes different equality patterns use different codes, with
no numerical coefficients present in the finite counting universe. -/
theorem patterns_le_columnCode {Pattern : Type*} [Fintype Pattern]
    (N segments omitted imperfect : ℕ)
    (encode : Pattern → ColumnCode N segments omitted imperfect)
    (decode : ColumnCode N segments omitted imperfect → Pattern)
    (hdecode : ∀ p, decode (encode p) = p) :
    Fintype.card Pattern ≤ 2 ^ (5 * N + 1) * N ^ (2 * segments + omitted + imperfect) := by
  apply (Fintype.card_le_of_injective encode ?_).trans (card_columnCode_le _ _ _ _)
  intro p q heq
  have h := congrArg decode heq
  simpa only [hdecode] using h

end TwoPointCorrelations

end OAI
