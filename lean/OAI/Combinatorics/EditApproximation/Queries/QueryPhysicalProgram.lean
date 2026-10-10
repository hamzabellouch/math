import OAI.Combinatorics.EditApproximation.Queries.QueryLocalProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalReaders

namespace OAI

/-! The full charged refinement program on physical ranked requests and
scalar source requests.  This connects the local Boolean implementation
to the same adaptive query used in the accuracy and dependency proofs. -/

namespace EditApproximation

section Physical
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
  (q : TargetInterval target.length)

def queryPhysicalRandomDataRequest :
    BitQuery (Sum σ {child : PhysicalTableRequest M J target.length //
      child.combinedRank T S < (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S})
      BinaryFraction :=
  queryLocalProgram source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    (fun r => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalWarmupRead copies pass copy T S t ht node q node le_rfl 0 (Nat.zero_le T) r))
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalMassRead copies pass copy T S t ht node hbelow q input))
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2))
    (fun key => BitQuery.mapKeysWithWork (fun key => (Sum.inl key, 1)) (readGroup key))
    (fun key range => BitQuery.mapKeysWithWork (fun key => (Sum.inl key, 1)) (readInteger key range)) q
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input))
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalCurrentRead copies pass copy T S t node hbelow q input))

theorem queryPhysicalRandomDataRequest_refines
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q)
      (physicalRandomDataRequestQuery source target N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value pass copy T S t ht node hbelow
        expectedGroup expectedInteger q) := by
  unfold queryPhysicalRandomDataRequest physicalRandomDataRequestQuery
  apply queryLocalProgram_refines
  · intro r
    exact (queryPhysicalWarmupRead_refines copies pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r).mapKeysWithWork _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalMassRead_refines copies pass copy T S t ht node hbelow q input).mapKeysWithWork
      _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalWarmupRead_refines copies pass copy T S t ht node q
      (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
      0 (Nat.zero_le T) input.2).mapKeysWithWork _ _ (fun _ => rfl)
  · intro key
    exact (hg key).mapKeysWithWork _ _ (fun _ => rfl)
  · intro key range
    exact (hz key range).mapKeysWithWork _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalEarlierRead_refines copies pass copy T S t node hbelow q input).mapKeysWithWork
      _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalCurrentRead_refines copies pass copy T S t node hbelow q input).mapKeysWithWork
      _ _ (fun _ => rfl)

end Physical
end EditApproximation

end OAI
