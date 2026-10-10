import OAI.NumberTheory.Ostmann.Arithmetic.MovingCoprimeDescent

namespace OAI

/-! # The original regular slot lists in every moving child -/

namespace Ostmann
open scoped Classical

/-- Current regular slots, before sampling at this node. -/
def MovingSlotData.regularSlots {σ : Type*} : {n : ℕ} → MovingSlotData σ n → List σ
  | _, .leaf _ regular => regular
  | _, .node _ CL CR _ _ _ => CL ++ CR

/-- The child regular slots contain the same compensation vector and the
corresponding parent's regular slots, with their actual per-leaf allocation. -/
def MovingSlotData.RegularCoherent {σ : Type*} : {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ CL CR U left right =>
      left.regularSlots.Perm (U ++ CL) ∧ right.regularSlots.Perm (U ++ CR) ∧
        left.RegularCoherent ∧ right.RegularCoherent

theorem flattenMovingSlots_append_perm {σ : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) :
    (flattenMovingSlots n (appendMovingSlotLeaves n x y)).Perm
      (flattenMovingSlots n x ++ flattenMovingSlots n y) := by
  apply List.perm_iff_count.mpr
  intro a
  induction n with
  | zero => simp [flattenMovingSlots, appendMovingSlotLeaves]
  | succ n ih =>
    have hx := ih x.1 y.1
    have hy := ih x.2 y.2
    simpa only [flattenMovingSlots, appendMovingSlotLeaves, List.count_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg₂ (· + ·) hx hy

theorem buildMovingSlotData_regular_perm {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).regularSlots.Perm
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) := by
  cases samples with
  | leaf => exact List.Perm.refl _
  | @node n samples left right =>
    apply List.perm_iff_count.mpr
    intro a
    simp only [buildMovingSlotData, MovingSlotData.regularSlots, flattenMovingSlots,
      List.count_append]
    omega

/-- Coherence is proved for the actual sampler, not supplied as a new
assumption about the original history. -/
theorem buildMovingSlotData_regular_coherent {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).RegularCoherent := by
  induction samples with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    let U := movingCompensationSlots n samples
    have hL := (buildMovingSlotData_regular_perm n t.2.1
      (appendMovingSlotLeaves n U small.1) bulk.1 left).trans
      ((flattenMovingSlots_append_perm n U small.1).append_right (flattenMovingSlots n bulk.1))
    have hR := (buildMovingSlotData_regular_perm n t.2.2
      (appendMovingSlotLeaves n U small.2) bulk.2 right).trans
      ((flattenMovingSlots_append_perm n U small.2).append_right (flattenMovingSlots n bulk.2))
    refine ⟨?_, ?_, ihL _ _ _, ihR _ _ _⟩
    · simpa only [List.append_assoc] using hL
    · simpa only [List.append_assoc] using hR

end Ostmann

end OAI
