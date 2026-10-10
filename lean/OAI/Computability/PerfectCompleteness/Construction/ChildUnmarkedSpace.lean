import OAI.Computability.PerfectCompleteness.Algebra.BilinearWitnessLemmas
import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Sampling.UniformChildSum

namespace OAI

section

namespace PerfectCompleteness.ChildUnmarkedSpace

open RecursiveSpaces TreeSourceSpaces PointwiseSpaces
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

def childMap (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch n)) : squareSpace (H (childSlots slots i)) →ₗ[F2] H slots where
  toFun v := ⟨PointwiseSpaces.pullback F2 (restrictChild slots i) v.val,
    child_square_le_H slots i (Submodule.mem_map_of_mem v.property)⟩
  map_add' v w := by apply Subtype.ext; rfl
  map_smul' c v := by apply Subtype.ext; rfl

@[simp] theorem childMap_apply
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch n)) (v : squareSpace (H (childSlots slots i))) (x : Domain slots) :
    (childMap slots i v).val x = v.val (restrictChild slots i x) := rfl

theorem assemble_eq_recursiveSum
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (v : (i : Fin (branch n)) → squareSpace (H (childSlots slots i))) :
    BilinearWitness.assemble (childMap slots) v =
      UniformChildSum.recursiveSum (LeafDomain slots) v := by
  apply Subtype.ext
  simp only [BilinearWitness.assemble, Submodule.coe_sum]
  rfl

theorem assemble_surjective
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    Function.Surjective (BilinearWitness.assemble (childMap slots)) := by
  intro v
  obtain ⟨w, hw⟩ := UniformChildSum.recursiveSum_surjective
    (𝕜 := F2) (LeafDomain slots) v
  exact ⟨w, (assemble_eq_recursiveSum slots w).trans hw⟩

def space (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (mask : Fin (branch n) → Bool) : Submodule F2 (H slots) :=
  ⨆ i, ⨆ (_ : mask i = false), LinearMap.range (childMap slots i)

theorem childMap_mem_space
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (mask : Fin (branch n) → Bool) (i : Fin (branch n)) (hi : mask i = false)
    (v : squareSpace (H (childSlots slots i))) : childMap slots i v ∈ space slots mask := by
  have hle : LinearMap.range (childMap slots i) ≤ space slots mask := by
    unfold space
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  exact hle ⟨v, rfl⟩

private theorem projection_self_map (s : MixedSupport.Slot)
    (p : MixedSupport.Projection s s) (x : s.Domain) : p.map x = x := by
  cases s <;> cases p <;> rfl

private theorem sourceProjection_self
    {slots : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (slots s k))
    (x : Domain slots) : sourceProjection p x = x := by
  funext s k
  exact projection_self_map (slots s k) (p s k) (x s k)

theorem squarePullback_surjective_of_eq
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (heq : projected = slots) : Function.Surjective (ChildBlockProjection.squarePullback p) := by
  subst projected
  intro v
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext x
  change v.val (sourceProjection p x) = v.val x
  rw [sourceProjection_self]

theorem childMap_pullback
    {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) (v : squareSpace (H (childSlots projected i))) :
    childMap slots i
        (ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection p i) v) =
      HPullback p (childMap projected i v) := by
  apply Subtype.ext
  funext x
  rfl

theorem childMap_mem_projected_range
    {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) (heq : childSlots projected i = childSlots slots i)
    (v : squareSpace (H (childSlots slots i))) :
    childMap slots i v ∈ LinearMap.range (HPullback p) := by
  obtain ⟨w, rfl⟩ := squarePullback_surjective_of_eq
    (ChildAssemblyProjection.childProjection p i) heq v
  exact ⟨childMap projected i w, (childMap_pullback p i w).symm⟩

theorem space_le_projected_range
    {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (mask : Fin (branch n) → Bool)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hkeep : ∀ i, mask i = false → childSlots projected i = childSlots slots i) :
    space slots mask ≤ LinearMap.range (HPullback p) := by
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  rintro _ ⟨v, rfl⟩
  exact childMap_mem_projected_range p i (hkeep i hi) v

end
end PerfectCompleteness.ChildUnmarkedSpace

end

end OAI
