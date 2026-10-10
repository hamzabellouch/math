import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeys
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Source draws and table requests share the same concrete binary memo.
Rank-zero sources are stored once; each tagged recursive request pays for
its tag construction before entering the shared dictionary. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*}



theorem bitBody_refines (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → BitQuery (Sum σ {key : κ // tableRank key < tableRank parent}) BinaryFraction)
    (expectedBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → BinaryFraction × ℕ)
    (hbody : ∀ parent, BitQuery.Refines (fun word value => word.value = value)
      (tableBody parent) (expectedBody parent)) (key : Sum σ κ) :
    BitQuery.Refines (fun word value => word.value = value)
      (bitBody tableRank tableBody sourceValue key)
      (body tableRank expectedBody (fun source => (sourceValue source).1.value) key) := by
  cases key with
  | inl source => exact .charge _ (.done rfl)
  | inr table =>
    exact (hbody table).mapKeysWithWork (fun key => (child tableRank table key, 1))
      (child tableRank table) (fun _ => rfl)

end EditApproximation.SourceRanked

end OAI
