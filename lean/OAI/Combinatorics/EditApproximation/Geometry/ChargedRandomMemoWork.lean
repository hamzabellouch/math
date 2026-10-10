import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomExpansion
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomMemo

namespace OAI

/-! Source reads and dictionary visits in the actual shared-cache evaluator
are bounded by the width of its projected table dependency expansion. -/

namespace EditApproximation

section Work

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "mixedProgram" => chargedRandomGlobalQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixedProgram sourceAnswer
local notation "values" => chargedRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

variable (hbody : ∀ (request : ChargedPhysicalRequest M J target.length passes copies T S),
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial request).value
    (Sum.elim sourceAnswer (fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
        tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta group integer initial request)

include hbody


 theorem chargedRandomMemoEvaluate_requests_le_widthWork
    (sourceBudget bits : ℕ)
    (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (hsource : ∀ key, (mixedProgram key).cost
      (Sum.elim sourceAnswer (fun next => values next.val))
      (Sum.elim (fun _ => 1) (fun _ => 0)) ≤ sourceBudget)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomMemoEvaluate source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode root).requests ≤
    (sourceBudget + 1) *
      (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork
          M source.length := by
  apply (SourceRanked.memo_requests_le_source_factor ChargedPhysicalRequest.rank mixedProgram
    sourceAnswer values hbody sourceBudget hsource bits encode hinjective hbounded root).trans
  apply Nat.mul_le_mul_left
  calc
    rankedUncachedCalls ChargedPhysicalRequest.rank program root =
        (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
          tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).nodeCount :=
      (queryDependencyExpansion_nodes depth index program
        (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
          tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root).symm
    _ ≤ _ := DependencyExpansion.nodeCount_le_widthWork _ _ _

 theorem chargedRandomMemoEvaluate_dictionaryVisits_le_widthWork
    (sourceBudget bits : ℕ)
    (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (hsource : ∀ key, (mixedProgram key).cost
      (Sum.elim sourceAnswer (fun next => values next.val))
      (Sum.elim (fun _ => 1) (fun _ => 0)) ≤ sourceBudget)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomMemoEvaluate source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode root).dictionaryVisits ≤
    (sourceBudget + 1) *
      (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork
          M source.length * (2 * (bits + 1)) := by
  exact (rankedMemoEvaluate_resource_bounds _ _ bits encode (.inr root) .empty).2.1.trans
    (Nat.mul_le_mul_right _
      (chargedRandomMemoEvaluate_requests_le_widthWork source target N P H T S passes copies
        factor multiplier tau eta kappa delta group integer initial readGroup readInteger sourceAnswer
        hbody sourceBudget bits encode hinjective hbounded hsource root))

end Work

end EditApproximation

end OAI
