import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementReadWork
import OAI.Combinatorics.EditApproximation.Geometry.WarmupQueryKeys

namespace OAI

/-! The dependency split for keys actually emitted by the adaptive local
queries. Current-index edges descend in the physical tree; older reads
decrease the table rank and never move to an ancestor. -/

namespace EditApproximation

namespace PhysicalTableRequest

def DependencyProgress {M J ny : ℕ} (T S : ℕ)
    (parent child : PhysicalTableRequest M J ny) : Prop :=
  (child.remainingDepth < parent.remainingDepth ∧ child.rank T S ≤ parent.rank T S) ∨
    (child.remainingDepth ≤ parent.remainingDepth ∧ child.rank T S < parent.rank T S)

theorem warmup_before_refinement_progress {M J ny : ℕ}
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (q r : TargetInterval ny) :
    DependencyProgress T S (refinement pass copy node T t q)
      (warmup pass copy otherNode j r) := by
  apply Or.inr
  refine ⟨remainingDepth_le_of_no_ancestor _ _ hnode, ?_⟩
  exact rank_lt_same_pass T S _ _ rfl (by change j < T + t; omega)

theorem refinement_child_same_progress {M J ny : ℕ}
    (pass copy T S t : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (i : Fin M) (q r : TargetInterval ny) :
    DependencyProgress T S (refinement pass copy node T t q)
      (refinement pass copy (physicalChild node hbelow i) T t r) := by
  apply Or.inl
  refine ⟨?_, le_rfl⟩
  apply remainingDepth_lt_of_descendant
  change node.1.val < node.1.val + 1
  omega

theorem refinement_child_earlier_progress {M J ny : ℕ}
    (pass copy T S t s : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (i : Fin M) (q r : TargetInterval ny) (hs : s < t) :
    DependencyProgress T S (refinement pass copy node T t q)
      (refinement pass copy (physicalChild node hbelow i) T s r) := by
  obtain ⟨hd, hr⟩ := refinement_history_child_progress pass copy T S t s node hbelow i q r hs
  exact Or.inr ⟨hd.le, hr⟩

theorem previous_pass_dependencyProgress {M J ny : ℕ}
    (T S : ℕ) (parent child : PhysicalTableRequest M J ny)
    (hpass : child.pass < parent.pass) (hindex : child.index ≤ T + S)
    (hnode : parent.node.1.val ≤ child.node.1.val) : DependencyProgress T S parent child :=
  Or.inr (previous_pass_progress T S parent child hpass hindex hnode)

theorem rank_lt_iff_index_lt_of_pass {M J ny : ℕ} (T S : ℕ)
    (parent child : PhysicalTableRequest M J ny) (hpass : child.pass = parent.pass) :
    child.rank T S < parent.rank T S ↔ child.index < parent.index := by
  unfold rank
  rw [hpass]
  omega

theorem rank_not_lt_iff_index_eq_of_pass {M J ny : ℕ} (T S : ℕ)
    (parent child : PhysicalTableRequest M J ny) (hpass : child.pass = parent.pass)
    (hindex : child.index ≤ parent.index) :
    ¬ child.rank T S < parent.rank T S ↔ child.index = parent.index := by
  rw [rank_lt_iff_index_lt_of_pass T S parent child hpass]
  omega

end PhysicalTableRequest

theorem physicalRefinementWarmupRead_keys_progress {M J ny : ℕ}
    (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    ∀ key ∈ (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).keys oracle,
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.refinement pass copy node T t q) key.val := by
  intro key hk
  simp only [physicalRefinementWarmupRead, FiniteQuery.keys, List.mem_singleton] at hk
  subst key
  exact PhysicalTableRequest.warmup_before_refinement_progress pass copy T S t ht
    node otherNode hnode j hj q r

theorem physicalRefinementDataRequest_keys_progress {α : Type*} (source target : List α) {M J : ℕ}
    (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).keys oracle,
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.refinement pass copy node T t q) key.val := by
  unfold physicalRefinementDataRequestQuery
  apply localRefinementDataQuery_keys_all
  · intro r key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r oracle key hk
  · intro input
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 oracle key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 oracle key hk
  · intro input key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact PhysicalTableRequest.refinement_child_earlier_progress pass copy T S t input.2.1
        node hbelow input.1 q input.2.2 hs
    · exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact PhysicalTableRequest.refinement_child_same_progress pass copy T S t node hbelow input.1 q input.2

theorem physicalRefinementWarmupRead_keys_pass_copy {M J ny : ℕ}
    (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    ∀ key ∈ (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).keys oracle,
      key.val.pass = pass ∧ key.val.copy = copy ∧ key.val.index ≤ T + t := by
  intro key hk
  simp only [physicalRefinementWarmupRead, FiniteQuery.keys, List.mem_singleton] at hk
  subst key
  exact ⟨rfl, rfl, hj.trans (Nat.le_add_right T t)⟩

theorem physicalRefinementDataRequest_keys_pass_copy {α : Type*} (source target : List α) {M J : ℕ}
    (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).keys oracle,
      key.val.pass = pass ∧ key.val.copy = copy ∧ key.val.index ≤ T + t := by
  unfold physicalRefinementDataRequestQuery
  apply localRefinementDataQuery_keys_all
  · intro r key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r oracle key hk
  · intro input
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 oracle key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 oracle key hk
  · intro input key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact ⟨rfl, rfl, by change T + input.2.1 ≤ T + t; omega⟩
    · exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact ⟨rfl, rfl, le_rfl⟩

theorem physicalWarmupRequestQuery_keys_progress {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (oracle)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle →
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.warmup pass copy node j q) key.val) :
    ∀ key ∈ (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).keys oracle,
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.warmup pass copy node j q) key.val := by
  cases j with
  | zero => exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed
  | succ j =>
    apply physicalWarmupRequestQuery_keys_all source target N P F A pass copy T S (j + 1) node q
      seedRead oracle _ hseed
    intro hbelow input
    obtain ⟨hd, hr⟩ := PhysicalTableRequest.warmup_previous_child_progress pass copy T S (j + 1)
      node hbelow input.1 q input.2 (Nat.succ_pos j)
    exact Or.inr ⟨hd.le, hr⟩

end EditApproximation

end OAI
