import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmup
import OAI.Combinatorics.EditApproximation.Geometry.DependencyExpansion
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Concrete table requests and their dependency order. A single table
index identifies the end of warmup with refinement time zero. Copy labels
remain part of a request but do not reset its dependency rank. -/

namespace EditApproximation





namespace PhysicalTableRequest

variable {M J ny : ℕ}











theorem refinement_zero_eq_warmup (pass copy : ℕ) (node : PhysicalNode M J)
    (T : ℕ) (state : TargetInterval ny) :
    refinement pass copy node T 0 state = warmup pass copy node T state := by
  simp only [refinement, warmup, Nat.add_zero]

def changeCopy (request : PhysicalTableRequest M J ny) (copy : ℕ) :
    PhysicalTableRequest M J ny := { request with copy := copy }

@[simp] theorem rank_changeCopy (T S : ℕ) (request : PhysicalTableRequest M J ny) (copy : ℕ) :
    rank T S (changeCopy request copy) = rank T S request := rfl

@[simp] theorem remainingDepth_changeCopy (request : PhysicalTableRequest M J ny) (copy : ℕ) :
    remainingDepth (changeCopy request copy) = remainingDepth request := rfl

@[simp] theorem warmup_rank (pass copy : ℕ) (node : PhysicalNode M J)
    (T S j : ℕ) (state : TargetInterval ny) :
    rank T S (warmup pass copy node j state) = pass * (T + S + 1) + j := rfl

@[simp] theorem refinement_rank (pass copy : ℕ) (node : PhysicalNode M J)
    (T S t : ℕ) (state : TargetInterval ny) :
    rank T S (refinement pass copy node T t state) = pass * (T + S + 1) + (T + t) := rfl

theorem remainingDepth_le_of_no_ancestor (first second : PhysicalTableRequest M J ny)
    (hnode : first.node.1.val ≤ second.node.1.val) :
    second.remainingDepth ≤ first.remainingDepth :=
  Nat.sub_le_sub_left hnode J

theorem remainingDepth_lt_of_descendant (first second : PhysicalTableRequest M J ny)
    (hnode : first.node.1.val < second.node.1.val) :
    second.remainingDepth < first.remainingDepth := by
  have hsecond : second.node.1.val ≤ J := Nat.le_of_lt_succ second.node.1.isLt
  unfold remainingDepth
  omega



theorem sameIndexChild_progress (T S : ℕ) (request : PhysicalTableRequest M J ny)
    (hbelow : request.node.1.val < J) (i : Fin M) (state : TargetInterval ny) :
    (sameIndexChild request hbelow i state).remainingDepth < request.remainingDepth ∧
      rank T S (sameIndexChild request hbelow i state) ≤ rank T S request := by
  constructor
  · unfold remainingDepth sameIndexChild physicalChild
    dsimp only
    omega
  · exact le_rfl

theorem rank_lt_same_pass (T S : ℕ) (first second : PhysicalTableRequest M J ny)
    (hpass : second.pass = first.pass) (hindex : second.index < first.index) :
    rank T S second < rank T S first := by
  unfold rank
  rw [hpass]
  exact Nat.add_lt_add_left hindex _

/-- A warmup predecessor lies at the physical child and at the preceding
unified table index. -/
theorem warmup_previous_child_progress (pass copy T S j : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (i : Fin M)
    (state previousState : TargetInterval ny) (hj : 0 < j) :
    (warmup pass copy (physicalChild node hbelow i) (j - 1) previousState).remainingDepth <
        (warmup pass copy node j state).remainingDepth ∧
      rank T S (warmup pass copy (physicalChild node hbelow i) (j - 1) previousState) <
        rank T S (warmup pass copy node j state) := by
  constructor
  · unfold remainingDepth warmup physicalChild
    dsimp only
    omega
  · dsimp only [rank, warmup]
    omega

/-- Old refinement values and all optimistic-history values have
strictly smaller rank, even if their copy label changes. -/
theorem refinement_history_progress (pass copy previousCopy T S t s : ℕ)
    (node previousNode : PhysicalNode M J) (state previousState : TargetInterval ny)
    (hnode : node.1.val ≤ previousNode.1.val) (hs : s < t) :
    (refinement pass previousCopy previousNode T s previousState).remainingDepth ≤
        (refinement pass copy node T t state).remainingDepth ∧
      rank T S (refinement pass previousCopy previousNode T s previousState) <
        rank T S (refinement pass copy node T t state) := by
  constructor
  · exact Nat.sub_le_sub_left hnode J
  · simp only [refinement_rank]
    omega

theorem refinement_history_child_progress (pass copy T S t s : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (i : Fin M)
    (state previousState : TargetInterval ny) (hs : s < t) :
    (refinement pass copy (physicalChild node hbelow i) T s previousState).remainingDepth <
        (refinement pass copy node T t state).remainingDepth ∧
      rank T S (refinement pass copy (physicalChild node hbelow i) T s previousState) <
        rank T S (refinement pass copy node T t state) := by
  constructor
  · unfold remainingDepth refinement physicalChild
    dsimp only
    omega
  · dsimp only [rank, refinement]
    omega

/-- A previous pass can request any of its warmup/refinement indices.
The added one in the pass stride makes its last index strictly earlier
than the next pass's first index. -/
theorem rank_lt_previous_pass (T S : ℕ) (first second : PhysicalTableRequest M J ny)
    (hpass : second.pass < first.pass) (hindex : second.index ≤ T + S) :
    rank T S second < rank T S first := by
  have hblock : second.pass * (T + S + 1) + second.index <
      (second.pass + 1) * (T + S + 1) := by
    nlinarith only [hindex]
  have hnext := Nat.mul_le_mul_right (T + S + 1) (Nat.succ_le_of_lt hpass)
  exact hblock.trans_le (hnext.trans (Nat.le_add_right _ _))

theorem previous_pass_progress (T S : ℕ) (first second : PhysicalTableRequest M J ny)
    (hpass : second.pass < first.pass) (hindex : second.index ≤ T + S)
    (hnode : first.node.1.val ≤ second.node.1.val) :
    second.remainingDepth ≤ first.remainingDepth ∧ rank T S second < rank T S first :=
  ⟨remainingDepth_le_of_no_ancestor first second hnode,
    rank_lt_previous_pass T S first second hpass hindex⟩

theorem rank_lt_pass_bound (T S passes : ℕ) (request : PhysicalTableRequest M J ny)
    (hpass : request.pass < passes) (hindex : request.index ≤ T + S) :
    rank T S request < passes * (T + S + 1) := by
  have hblock : request.pass * (T + S + 1) + request.index <
      (request.pass + 1) * (T + S + 1) := by
    nlinarith only [hindex]
  exact hblock.trans_le (Nat.mul_le_mul_right (T + S + 1) (Nat.succ_le_of_lt hpass))

theorem warmup_index_bound (pass copy : ℕ) (node : PhysicalNode M J)
    (T S j : ℕ) (state : TargetInterval ny) (hj : j ≤ T) :
    (warmup pass copy node j state).index ≤ T + S := by
  change j ≤ T + S
  omega

theorem refinement_index_bound (pass copy : ℕ) (node : PhysicalNode M J)
    (T S t : ℕ) (state : TargetInterval ny) (ht : t ≤ S) :
    (refinement pass copy node T t state).index ≤ T + S := by
  change T + t ≤ T + S
  omega

theorem warmup_bounded (passes copies pass copy : ℕ) (node : PhysicalNode M J)
    (T S j : ℕ) (state : TargetInterval ny)
    (hpass : pass < passes) (hcopy : copy < copies) (hj : j ≤ T) :
    Bounded passes copies T S (warmup pass copy node j state) :=
  ⟨hpass, hcopy, warmup_index_bound pass copy node T S j state hj⟩

theorem refinement_bounded (passes copies pass copy : ℕ) (node : PhysicalNode M J)
    (T S t : ℕ) (state : TargetInterval ny)
    (hpass : pass < passes) (hcopy : copy < copies) (ht : t ≤ S) :
    Bounded passes copies T S (refinement pass copy node T t state) :=
  ⟨hpass, hcopy, refinement_index_bound pass copy node T S t state ht⟩

theorem bounded_changeCopy (passes copies T S : ℕ) (request : PhysicalTableRequest M J ny)
    (hrequest : Bounded passes copies T S request) (copy : ℕ) (hcopy : copy < copies) :
    Bounded passes copies T S (changeCopy request copy) :=
  ⟨hrequest.1, hcopy, hrequest.2.2⟩

theorem bounded_sameIndexChild (passes copies T S : ℕ) (request : PhysicalTableRequest M J ny)
    (hrequest : Bounded passes copies T S request)
    (hbelow : request.node.1.val < J) (i : Fin M) (state : TargetInterval ny) :
    Bounded passes copies T S (sameIndexChild request hbelow i state) := hrequest

theorem bounded_of_earlier_same_pass (passes copies T S : ℕ)
    (first second : PhysicalTableRequest M J ny) (hfirst : Bounded passes copies T S first)
    (hpass : second.pass = first.pass) (hcopy : second.copy < copies)
    (hindex : second.index ≤ first.index) : Bounded passes copies T S second := by
  exact ⟨hpass.symm ▸ hfirst.1, hcopy, hindex.trans hfirst.2.2⟩

theorem bounded_of_previous_pass (passes copies T S : ℕ)
    (first second : PhysicalTableRequest M J ny) (hfirst : Bounded passes copies T S first)
    (hpass : second.pass < first.pass) (hcopy : second.copy < copies)
    (hindex : second.index ≤ T + S) : Bounded passes copies T S second :=
  ⟨hpass.trans hfirst.1, hcopy, hindex⟩

/-- Bounded requests have an explicit finite coordinate representation;
the copy coordinate is retained even though the progress rank ignores it. -/
def boundedTuple (passes copies T S : ℕ)
    (request : {r : PhysicalTableRequest M J ny // Bounded passes copies T S r}) :
    Fin passes × Fin copies × PhysicalNode M J × Fin (T + S + 1) × TargetInterval ny :=
  (⟨request.1.pass, request.2.1⟩, ⟨request.1.copy, request.2.2.1⟩, request.1.node,
    ⟨request.1.index, Nat.lt_succ_of_le request.2.2.2⟩, request.1.state)

theorem boundedTuple_injective (passes copies T S : ℕ) :
    Function.Injective (@boundedTuple M J ny passes copies T S) := by
  intro first second heq
  apply Subtype.ext
  have hpass := congrArg (fun t => t.1.val) heq
  have hcopy := congrArg (fun t => t.2.1.val) heq
  have hnode := congrArg (fun t => t.2.2.1) heq
  have hindex := congrArg (fun t => t.2.2.2.1.val) heq
  have hstate := congrArg (fun t => t.2.2.2.2) heq
  cases first with
  | mk first hf =>
    cases second with
    | mk second hs =>
      cases first
      cases second
      simp only [boundedTuple] at hpass hcopy hnode hindex hstate
      cases hpass
      cases hcopy
      cases hnode
      cases hindex
      cases hstate
      rfl

instance boundedRequestFinite (passes copies T S : ℕ) :
    Finite {r : PhysicalTableRequest M J ny // Bounded passes copies T S r} :=
  Finite.of_injective (boundedTuple passes copies T S) (boundedTuple_injective passes copies T S)

end PhysicalTableRequest
end EditApproximation

end OAI
