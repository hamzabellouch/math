import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRequestEncoding
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 def capacity (M J ny passes copies T S : ℕ) : ℕ :=
  2 * (PhysicalTableRequest.entryCapacity M J ny +
    PhysicalTableRequest.capacity M J ny passes copies T S)

 def bits (M J ny passes copies T S : ℕ) : ℕ :=
  Nat.clog 2 (capacity M J ny passes copies T S + 1)

 theorem code_injective {M J ny passes copies T S : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@code M J ny passes copies T S) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hentry : physicalEntryCode left = physicalEntryCode right := by
        change 2 * physicalEntryCode left = 2 * physicalEntryCode right at heq
        omega
      exact congrArg Sum.inl (physicalEntryCode_injective hM hentry)
    | inr right =>
      change 2 * physicalEntryCode left = 2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * PhysicalTableRequest.code copies T S left.val + 1 = 2 * physicalEntryCode right at heq
      omega
    | inr right =>
      have htable : PhysicalTableRequest.code copies T S left.val =
          PhysicalTableRequest.code copies T S right.val := by
        change 2 * PhysicalTableRequest.code copies T S left.val + 1 =
          2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
        omega
      exact congrArg Sum.inr (PhysicalTableRequest.code_injective hM passes copies T S htable)

 theorem code_bound {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < capacity M J ny passes copies T S := by
  cases request with
  | inl entry =>
    have h := physicalEntryCode_bound hM entry
    change physicalEntryCode entry < PhysicalTableRequest.entryCapacity M J ny at h
    simp only [code, capacity]
    omega
  | inr request =>
    have h := PhysicalTableRequest.code_bound hM passes copies T S request.val request.property
    simp only [code, capacity]
    omega

 theorem code_fits {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < 2 ^ bits M J ny passes copies T S :=
  (code_bound hM request).trans_le
    ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))

 theorem coarse_rank_lt {M J ny passes copies T S : ℕ} (entry : PhysicalEntry M J ny)
    (request : {request : PhysicalTableRequest M J ny // request.Bounded passes copies T S})
    (hnode : entry.1 = request.val.node) :
    rank (Sum.inl entry : ChargedPhysicalRequest M J ny passes copies T S) < rank (Sum.inr request) := by
  change J - entry.1.1.val + 0 < request.val.remainingDepth + (request.val.rank T S + 1)
  rw [hnode]
  unfold PhysicalTableRequest.remainingDepth
  omega

 theorem table_rank_lt {M J ny passes copies T S : ℕ}
    (parent child : {request : PhysicalTableRequest M J ny // request.Bounded passes copies T S})
    (h : child.val.combinedRank T S < parent.val.combinedRank T S) :
    rank (Sum.inr child : ChargedPhysicalRequest M J ny passes copies T S) < rank (Sum.inr parent) := by
  simpa only [rank, depth, index, ← Nat.add_assoc, PhysicalTableRequest.combinedRank] using
    Nat.add_lt_add_right h 1

end ChargedPhysicalRequest

end EditApproximation

end OAI
