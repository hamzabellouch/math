import OAI.Combinatorics.EditApproximation.Geometry.SourceErasure
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryCostOrder

namespace OAI

/-! Source leaves add only their executed read count to each table body.
Projecting them away preserves the table dependency program, so a uniform
local source budget multiplies its uncached request bound. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ)
  (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
  (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
  (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
    tableValue key)

def projectedBody (key : κ) : FiniteQuery {next : κ // tableRank next < tableRank key} :=
  FiniteQuery.eraseSources sourceValue (tableBody key)

include hbody in
 theorem projectedBody_value (key : κ) :
    (projectedBody tableRank tableBody sourceValue key).value (fun next => tableValue next.val) =
      tableValue key :=
  (FiniteQuery.eraseSources_value sourceValue _ (tableBody key)).trans (hbody key)

include hbody in
 theorem projectedProgram_value (key : κ) :
    rankedProgramValue tableRank (projectedBody tableRank tableBody sourceValue) key = tableValue key :=
  rankedProgramValue_eq tableRank _ tableValue
    (projectedBody_value tableRank tableBody sourceValue tableValue hbody) key

include hbody in
 theorem uncachedCalls_le_source_factor (sourceBudget : ℕ)
    (hsource : ∀ key, (tableBody key).cost
      (Sum.elim sourceValue (fun next => tableValue next.val)) (Sum.elim (fun _ => 1) (fun _ => 0)) ≤
        sourceBudget) (key : κ) :
    rankedUncachedCalls (rank tableRank) (body tableRank tableBody sourceValue) (.inr key) ≤
      (sourceBudget + 1) *
        rankedUncachedCalls tableRank (projectedBody tableRank tableBody sourceValue) key := by
  let mixed := body tableRank tableBody sourceValue
  let projected := projectedBody tableRank tableBody sourceValue
  let W := rankedUncachedCalls tableRank projected
  have hvalue (next : Sum σ κ) :
      rankedProgramValue (rank tableRank) mixed next = value sourceValue tableValue next :=
    program_value tableRank tableBody sourceValue tableValue hbody next
  have hpvalue (next : κ) : rankedProgramValue tableRank projected next = tableValue next :=
    projectedProgram_value tableRank tableBody sourceValue tableValue hbody next
  have hW (parent : κ) : W parent = (projected parent).cost
      (fun next => tableValue next.val) (fun next => W next.val) + 1 := by
    dsimp only [W]
    rw [rankedUncachedCalls]
    simp only [hpvalue]
  have hall : ∀ level parent, tableRank parent = level →
      rankedUncachedCalls (rank tableRank) mixed (.inr parent) ≤ (sourceBudget + 1) * W parent := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro parent hlevel
      have horacle :
          (fun next => rankedProgramValue (rank tableRank) mixed next.val) ∘ child tableRank parent =
          Sum.elim sourceValue (fun next => tableValue next.val) := by
        funext next
        rw [Function.comp_apply, hvalue]
        cases next <;> rfl
      have hcost := FiniteQuery.cost_mono_weights
        (Sum.elim sourceValue (fun next => tableValue next.val)) (tableBody parent)
        (fun next => rankedUncachedCalls (rank tableRank) mixed (child tableRank parent next).val)
        (Sum.elim (fun _ => 1) (fun next => (sourceBudget + 1) * W next.val)) (by
          intro next
          cases next with
          | inl source =>
            change rankedUncachedCalls (rank tableRank) mixed (.inl source) ≤ 1
            rw [rankedUncachedCalls]
            exact le_rfl
          | inr next =>
            exact ih (tableRank next.val) (hlevel ▸ next.property) next.val rfl)
      have hsplit : (tableBody parent).cost
          (Sum.elim sourceValue (fun next => tableValue next.val))
          (Sum.elim (fun _ => 1) (fun next => (sourceBudget + 1) * W next.val)) =
          (tableBody parent).cost (Sum.elim sourceValue (fun next => tableValue next.val))
            (Sum.elim (fun _ => 1) (fun _ => 0)) +
          (sourceBudget + 1) * (projected parent).cost
            (fun next => tableValue next.val) (fun next => W next.val) := by
        rw [FiniteQuery.cost_source_table, FiniteQuery.cost_mul_weight]
        rfl
      change rankedUncachedCalls (rank tableRank) (body tableRank tableBody sourceValue) (.inr parent) ≤ _
      rw [rankedUncachedCalls]
      change (FiniteQuery.mapKeys (child tableRank parent) (tableBody parent)).cost
        (fun next => rankedProgramValue (rank tableRank) mixed next.val)
        (fun next => rankedUncachedCalls (rank tableRank) mixed next.val) + 1 ≤ _
      rw [FiniteQuery.mapKeys_cost, horacle]
      calc
        _ ≤ (tableBody parent).cost
            (Sum.elim sourceValue (fun next => tableValue next.val))
            (Sum.elim (fun _ => 1) (fun next => (sourceBudget + 1) * W next.val)) + 1 :=
          Nat.add_le_add_right hcost 1
        _ = (tableBody parent).cost (Sum.elim sourceValue (fun next => tableValue next.val))
            (Sum.elim (fun _ => 1) (fun _ => 0)) +
            (sourceBudget + 1) * (projected parent).cost
              (fun next => tableValue next.val) (fun next => W next.val) + 1 := by rw [hsplit]
        _ ≤ sourceBudget + (sourceBudget + 1) * (projected parent).cost
              (fun next => tableValue next.val) (fun next => W next.val) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add_right (hsource parent) _) _
        _ = (sourceBudget + 1) * W parent := by rw [hW]; ring
  exact hall (tableRank key) key rfl

include hbody in
 theorem memo_requests_le_source_factor (sourceBudget : ℕ)
    (hsource : ∀ key, (tableBody key).cost
      (Sum.elim sourceValue (fun next => tableValue next.val)) (Sum.elim (fun _ => 1) (fun _ => 0)) ≤
        sourceBudget)
    (bits : ℕ) (encode : Sum σ κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) :
    (rankedMemoEvaluate (rank tableRank) (body tableRank tableBody sourceValue)
      bits encode (.inr key) .empty).requests ≤
      (sourceBudget + 1) *
        rankedUncachedCalls tableRank (projectedBody tableRank tableBody sourceValue) key :=
  (rankedMemoEvaluate_requests_le _ _ bits encode hinjective hbounded (.inr key) .empty
    (memoSound_empty _ _ _)).trans
      (uncachedCalls_le_source_factor tableRank tableBody sourceValue tableValue hbody
        sourceBudget hsource key)

end EditApproximation.SourceRanked

end OAI
