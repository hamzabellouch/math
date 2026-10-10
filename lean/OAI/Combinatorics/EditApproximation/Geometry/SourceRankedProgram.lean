import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryRestriction
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoSimulation
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Random source coordinates and recursive table entries share the same
memo evaluator. Source coordinates have rank zero; each table rank is
shifted by one. Consequently repeated source reads reuse their stored draw. -/

namespace EditApproximation

namespace SourceRanked

variable {σ κ : Type*}







def value (sourceValue : σ → ℚ) (tableValue : κ → ℚ) : Sum σ κ → ℚ :=
  Sum.elim sourceValue tableValue

 theorem body_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (key : Sum σ κ) :
    (body tableRank tableBody sourceValue key).value
      (fun next => value sourceValue tableValue next.val) = value sourceValue tableValue key := by
  cases key with
  | inl source => rfl
  | inr table =>
    rw [body, FiniteQuery.mapKeys_value]
    have horacle : (fun next => value sourceValue tableValue next.val) ∘ child tableRank table =
        Sum.elim sourceValue (fun next => tableValue next.val) := by
      funext next
      cases next <;> rfl
    rw [horacle]
    exact hbody table

 theorem program_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (key : Sum σ κ) :
    rankedProgramValue (rank tableRank) (body tableRank tableBody sourceValue) key =
      value sourceValue tableValue key :=
  rankedProgramValue_eq _ _ _ (body_value tableRank tableBody sourceValue tableValue hbody) key

 theorem memo_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (bits : ℕ) (encode : Sum σ κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (key : Sum σ κ) :
    (rankedMemoEvaluate (rank tableRank) (body tableRank tableBody sourceValue)
      bits encode key .empty).value = value sourceValue tableValue key := by
  rw [rankedMemoEvaluate_empty _ _ bits encode hinjective hbounded]
  exact program_value tableRank tableBody sourceValue tableValue hbody key

end SourceRanked

end EditApproximation

end OAI
