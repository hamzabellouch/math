import OAI.Combinatorics.EditApproximation.Queries.QuerySourceWidths
import OAI.Combinatorics.EditApproximation.Queries.QueryRestrictionCost

namespace OAI

namespace EditApproximation
section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

abbrev QueryBoundedChild := Sum σ {child : {r : PhysicalTableRequest M J n //
  r.Bounded passes copies T S} // child.val.combinedRank T S < parent.val.combinedRank T S}

def queryRestrictedPhysicalOracle (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction) :
    QueryPhysicalChild (σ := σ) passes copies T S parent → BinaryFraction :=
  BitQuery.restrictedOracle _ (querySupportedChildWithWork passes copies T S parent)
    (querySupportedChildWithWork_value passes copies T S parent)
    (fun key => oracle (SourceRanked.supportedChildMap (PhysicalTableRequest.combinedRank T S)
      (PhysicalTableRequest.Bounded passes copies T S) parent key))

def queryRestrictedPhysicalReadWork (readWork : QueryBoundedChild (σ := σ) passes copies T S parent → ℕ) :
    QueryPhysicalChild (σ := σ) passes copies T S parent → ℕ :=
  BitQuery.restrictedReadWork _ (querySupportedChildWithWork passes copies T S parent)
    (querySupportedChildWithWork_value passes copies T S parent)
    (fun key => 1 + readWork (SourceRanked.supportedChildMap (PhysicalTableRequest.combinedRank T S)
      (PhysicalTableRequest.Bounded passes copies T S) parent key))

theorem queryRestrictPhysicalBody_work
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (readWork : QueryBoundedChild (σ := σ) passes copies T S parent → ℕ) :
    (queryRestrictPhysicalBody passes copies T S parent program).work oracle readWork =
      program.work (queryRestrictedPhysicalOracle passes copies T S parent oracle)
        (queryRestrictedPhysicalReadWork passes copies T S parent readWork) := by
  rw [queryRestrictPhysicalBody, BitQuery.mapKeysWithWork_work, BitQuery.restrictWithWork_work]
  rfl

theorem queryRestrictPhysicalBody_value
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction) :
    (queryRestrictPhysicalBody passes copies T S parent program).value oracle =
      program.value (queryRestrictedPhysicalOracle passes copies T S parent oracle) := by
  rw [queryRestrictPhysicalBody, BitQuery.mapKeysWithWork_value, BitQuery.restrictWithWork_value]
  rfl

theorem queryRestrictedPhysicalOracle_table_width
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (B : ℕ) (hB : 2 ≤ B) (hw : ∀ key, (oracle (Sum.inr key)).width ≤ B) (child) :
    (queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child)).width ≤ B := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  split
  · exact hw _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hB)

theorem queryRestrictedPhysicalOracle_table_nonneg
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (hn : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) (child) :
    0 ≤ (queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child)).value := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  split
  · exact hn _
  · simp only [BinaryFraction.nat_value, Nat.cast_zero, le_refl]

theorem queryRestrictedPhysicalOracle_width
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (B : ℕ) (hB : 2 ≤ B) (hw : ∀ key, (oracle key).width ≤ B) (key) :
    (queryRestrictedPhysicalOracle passes copies T S parent oracle key).width ≤ B :=
  BitQuery.restrictedOracle_width _ _ _ _ B hB (fun _ => hw _) key

@[simp] theorem queryRestrictedPhysicalOracle_source
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction) (source : σ) :
    queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inl source) = oracle (Sum.inl source) := rfl

theorem queryRestrictedPhysicalOracle_table
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.val.combinedRank T S})
    (hb : child.val.Bounded passes copies T S) :
    queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child) =
      oracle (Sum.inr ⟨⟨child.val, hb⟩, child.property⟩) := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  rw [dite_eq_left ((querySupportedChildWithWork_value passes copies T S parent (Sum.inr child)).mpr hb)]
  rfl

private theorem index_le_combinedRank (request : PhysicalTableRequest M J n) :
    request.index ≤ request.combinedRank T S := by
  unfold PhysicalTableRequest.combinedRank PhysicalTableRequest.rank
  omega

private theorem pass_le_combinedRank (request : PhysicalTableRequest M J n) :
    request.pass ≤ request.combinedRank T S := by
  have hmul : request.pass ≤ request.pass * (T + S + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold PhysicalTableRequest.combinedRank PhysicalTableRequest.rank
  omega

theorem queryRestrictedPhysicalReadWork_bound
    (readWork : QueryBoundedChild (σ := σ) passes copies T S parent → ℕ) (B W : ℕ)
    (hp : Nat.size passes ≤ B) (hc : Nat.size copies ≤ B) (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hr : Nat.size (parent.val.combinedRank T S) ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hW : ∀ key, readWork key ≤ W)
    (key : QueryPhysicalChild (σ := σ) passes copies T S parent)
    (hk : ∀ child, key = Sum.inr child → child.val.copy = parent.val.copy) :
    queryRestrictedPhysicalReadWork passes copies T S parent readWork key ≤ 50 * B + 21 + W := by
  have hread (k) := hW (SourceRanked.supportedChildMap (PhysicalTableRequest.combinedRank T S)
    (PhysicalTableRequest.Bounded passes copies T S) parent k)
  cases key with
  | inl source =>
    change 1 + (1 + readWork _) ≤ _
    have := hread ⟨Sum.inl source, trivial⟩
    omega
  | inr child =>
    have hpass : Nat.size child.val.pass ≤ B :=
      (Nat.size_le_size ((pass_le_combinedRank T S child.val).trans child.property.le)).trans hr
    have hindex : Nat.size child.val.index ≤ B :=
      (Nat.size_le_size ((index_le_combinedRank T S child.val).trans child.property.le)).trans hr
    have hcopy' : Nat.size child.val.copy ≤ B := by rw [hk child rfl]; exact hcopy
    have hguard := queryPhysicalBoundedWithWork_cost passes copies T S B child.val hp hc hT hS hpass hcopy' hindex
    unfold queryRestrictedPhysicalReadWork BitQuery.restrictedReadWork
    change (querySupportedChildWithWork (σ := σ) passes copies T S parent (Sum.inr child)).2 ≤ 50 * B + 20 at hguard
    by_cases hgate : (querySupportedChildWithWork (σ := σ) passes copies T S parent (Sum.inr child)).1 = true
    · rw [dite_eq_left hgate]
      dsimp only
      have := hread ⟨Sum.inr child, (querySupportedChildWithWork_value passes copies T S parent _).mp hgate⟩
      omega
    · rw [dite_eq_right hgate]
      omega

end Body
end EditApproximation

end OAI
