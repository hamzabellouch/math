import OAI.Combinatorics.EditApproximation.Queries.QueryProgramWidth
import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyRefinementCost

namespace OAI

namespace EditApproximation
open BinaryFraction

section Physical
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
  (q : TargetInterval target.length)
  (oracle : Sum σ {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)

theorem queryPhysicalRandomDataRequest_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q).value oracle).width ≤
      preparedKernelWordBudget M B := by
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgram_width source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t _ _ _ _ _ q _ _ oracle B
    hn.largeBits hn.inputSize (by have := hn.sourceSize; omega) hn.targetSize
    (by have := hn.aritySize; omega) (by have := hn.precisionSize; omega) hn.factorSize htime hn.factorWidth hn.decrementSize
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact hv _
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact hnonneg _
  · intro key
    rw [BitQuery.mapKeysWithWork_value]
    exact queryPhysicalEarlierRead_width copies pass copy T S t node hbelow q
      (fun key => oracle (Sum.inr key)) B (by have := hn.largeBits; omega) hv key
  · intro key
    rw [BitQuery.mapKeysWithWork_value]
    exact hv _

end Physical

section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R) (q : TargetInterval target.length)
  (oracle : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)

theorem queryFamilyRefinement_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      passes copies pass copy T S t ht node hbelow time q).value oracle).width ≤
      preparedKernelWordBudget M B := by
  unfold queryFamilyRefinement
  exact queryPhysicalRandomDataRequest_width source target N P F exponent H Q eM eF B E Scale
    hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow _ _ q oracle hn htime hv hnonneg

end Family
end EditApproximation

end OAI
