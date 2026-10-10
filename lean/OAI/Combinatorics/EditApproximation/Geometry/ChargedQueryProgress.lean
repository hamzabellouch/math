import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Geometry.GlobalQueryProgress
import OAI.Combinatorics.EditApproximation.Queries.QueryDependencyExpansion

namespace OAI

/-! Every actual charged edge either descends at the current index or
uses a strictly earlier index without moving to an ancestor. Coarse
leaves retain their physical depth for source-width accounting. -/

namespace EditApproximation

namespace ChargedPhysicalRequest

def DependencyProgress {M J ny passes copies T S : ℕ}
    (parent child : ChargedPhysicalRequest M J ny passes copies T S) : Prop :=
  (child.depth < parent.depth ∧ child.index ≤ parent.index) ∨
    (child.depth ≤ parent.depth ∧ child.index < parent.index)

theorem table_progress {M J ny passes copies T S : ℕ}
    (parent child : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (h : PhysicalTableRequest.DependencyProgress T S parent.val child.val) :
    DependencyProgress (Sum.inr parent) (Sum.inr child) := by
  rcases h with h | h
  · exact Or.inl ⟨h.1, Nat.add_le_add_right h.2 1⟩
  · exact Or.inr ⟨h.1, Nat.add_lt_add_right h.2 1⟩

end ChargedPhysicalRequest

theorem chargedSeedQuery_keys_earlier {M J ny passes copies T S : ℕ}
    (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : PhysicalEntry M J ny) (oracle) :
    ∀ key ∈ (chargedSeedQuery N multiplier parent state).keys oracle,
      key.val.depth ≤ ChargedPhysicalRequest.depth (Sum.inr parent) ∧
        key.val.index < ChargedPhysicalRequest.index (Sum.inr parent) := by
  unfold chargedSeedQuery
  split_ifs with hn hp
  · intro key hk
    simp only [FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    constructor
    · change J - state.1.1.val ≤ J - parent.val.node.1.val
      rw [hn]
    · change 0 < parent.val.rank T S + 1
      omega
  · apply FiniteQuery.keys_all_collect
    · intro copy _ key hk
      simp only [chargedPreviousRead, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      have h := previousPassRequest_progress T S copy.val parent.val (Nat.pos_of_ne_zero hp) state.2
      exact ⟨h.1.le, Nat.add_lt_add_right h.2 1⟩
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro key hk
    exact False.elim (List.not_mem_nil hk)

theorem chargedWarmupQuery_keys_earlier {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (oracle) :
    ∀ key ∈ (chargedWarmupQuery source target N P F factor multiplier parent).keys oracle,
      key.val.depth ≤ ChargedPhysicalRequest.depth (Sum.inr parent) ∧
        key.val.index < ChargedPhysicalRequest.index (Sum.inr parent) := by
  have hseed (q : TargetInterval target.length) :=
    chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) oracle
  unfold chargedWarmupQuery
  split_ifs with hz hb hs
  · exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed
  · exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed
  · unfold physicalWarmupStepQuery
    apply localWarmupStepQuery_keys_all
    · intro q
      exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed
    · intro input key hk
      simp only [chargedWarmupChild, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      have h := PhysicalTableRequest.warmup_previous_child_progress parent.val.pass parent.val.copy T S
        parent.val.index parent.val.node hb input.1 parent.val.state input.2 (Nat.pos_of_ne_zero hz)
      exact ⟨h.1.le, Nat.add_lt_add_right h.2 1⟩
  · exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed

section Global

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem chargedGlobalQuery_keys_progress (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    ∀ key ∈ (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).keys
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val),
      ChargedPhysicalRequest.DependencyProgress request key.val := by
  cases request with
  | inl entry =>
    intro key hk
    exact False.elim (List.not_mem_nil hk)
  | inr parent =>
    unfold chargedGlobalQuery
    dsimp only
    split_ifs with hi hb hs
    · intro key hk
      exact Or.inr (chargedWarmupQuery_keys_earlier source target N P F factor multiplier parent _ key hk)
    · intro key hk
      apply Or.inr
      apply physicalInitialQuery_keys_all source target N P F _ _ _ _ _ _ _ key hk
      intro q
      exact chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) _
    · rw [FiniteQuery.mapKeys_keys]
      intro key hk
      obtain ⟨child, hc, rfl⟩ := List.mem_map.mp hk
      exact ChargedPhysicalRequest.table_progress parent child.val
        (physicalBoundedQuery_keys_progress source target N P F exponent H Q T S passes copies factor multiplier
          tau eta kappa delta group integer initial parent child hc)
    · intro key hk
      apply Or.inr
      apply physicalInitialQuery_keys_all source target N P F _ _ _ _ _ _ _ key hk
      intro q
      exact chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) _

end Global

end EditApproximation

end OAI
