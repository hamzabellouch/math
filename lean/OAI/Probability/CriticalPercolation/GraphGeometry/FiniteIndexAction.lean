import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphActionCoordinates

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ Q : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma finite_orbit_quotient_of_representatives (S : Set V) (hS : S.Finite)
    (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    Finite (MulAction.orbitRel.Quotient Λ V) := by
  let : Setoid V := MulAction.orbitRel Λ V
  let _ := hS.to_subtype
  apply Finite.of_surjective (fun s : S => Quotient.mk' s.val)
  intro q
  induction q using Quotient.inductionOn with
  | h v =>
    obtain ⟨s,hs,hvs⟩ := hcover v
    exact ⟨⟨s,hs⟩,Quotient.sound ((MulAction.orbitRel Λ V).symm (MulAction.orbitRel_apply.mpr hvs))⟩

lemma finite_representatives_of_orbit_quotient
    [Finite (MulAction.orbitRel.Quotient Λ V)] :
    ∃ S : Set V, S.Finite ∧ (∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) := by
  let : Setoid V := MulAction.orbitRel Λ V
  let S := Set.range (Quotient.out : MulAction.orbitRel.Quotient Λ V → V)
  refine ⟨S,Set.finite_range _,?_⟩
  intro v
  refine ⟨Quotient.out (Quotient.mk' v),⟨Quotient.mk' v,rfl⟩,?_⟩
  apply MulAction.orbitRel_apply.mp
  exact Quotient.exact' (Quotient.out_eq' (Quotient.mk' v)).symm

lemma finiteIndex_action_representatives (S : Set V) (hS : S.Finite)
    (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (L : Subgroup Λ) (hL : L.index≠0) :
    ∃ R : Set V, R.Finite ∧ (∀ v, ∃ r∈R, v∈MulAction.orbit L r) := by
  let _ := finite_orbit_quotient_of_representatives S hS hcover
  let _ := L.finite_quotient_of_finite_quotient_of_index_ne_zero (X := V) hL
  exact finite_representatives_of_orbit_quotient

def quotientSubgroupMap (ρ : Λ →* Q) (N : Subgroup Q) : N.comap ρ →* N where
  toFun g := ⟨ρ g.val,g.property⟩
  map_one' := Subtype.ext (ρ.map_one)
  map_mul' g h := Subtype.ext (ρ.map_mul g.val h.val)

lemma quotientSubgroupMap_surjective (ρ : Λ →* Q) (hρ : Surjective ρ)
    (N : Subgroup Q) : Surjective (quotientSubgroupMap ρ N) := by
  intro n
  obtain ⟨g,hg⟩ := hρ n.val
  exact ⟨⟨g,by change ρ g∈N; rw [hg]; exact n.property⟩,Subtype.ext hg⟩

lemma quotientSubgroupMap_kernel_orbits (ρ : Λ →* Q) (N : Subgroup Q)
    (hf : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) :
    ∀ v : V, (MulAction.orbit (quotientSubgroupMap ρ N).ker v).Finite := by
  intro v
  apply (hf v).subset
  rintro w ⟨g,hg⟩
  exact ⟨⟨g.val.val,congrArg Subtype.val g.property⟩,hg⟩

lemma quotientSubgroupMap_stabilizer_images (ρ : Λ →* Q) (N : Subgroup Q)
    (hf : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set Q).Finite) :
    ∀ v : V, ((MulAction.stabilizer (N.comap ρ) v).map
      (quotientSubgroupMap ρ N) : Set N).Finite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hf v)).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g.val,hg,rfl⟩

lemma subgroup_preservesEnds (ha : G.PreservesEnds (Λ := Λ)) (L : Subgroup Λ) :
    G.PreservesEnds (Λ := L) := fun g e => ha g.val e

lemma finiteIndex_quotient_transfer
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* Q) (hρ : Surjective ρ)
    (hf : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hs : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set Q).Finite)
    (N : Subgroup Q) (hN : N.index≠0) :
    G.PreservesEnds (Λ := N.comap ρ) ∧
      (∃ R : Set V, R.Finite ∧ ∀ v, ∃ r∈R, v∈MulAction.orbit (N.comap ρ) r) ∧
      Surjective (quotientSubgroupMap ρ N) ∧
      (∀ v : V, (MulAction.orbit (quotientSubgroupMap ρ N).ker v).Finite) ∧
      (∀ v : V, ((MulAction.stabilizer (N.comap ρ) v).map
        (quotientSubgroupMap ρ N) : Set N).Finite) := by
  refine ⟨G.subgroup_preservesEnds ha (N.comap ρ),?_,
    quotientSubgroupMap_surjective ρ hρ N,
    quotientSubgroupMap_kernel_orbits ρ N hf,
    quotientSubgroupMap_stabilizer_images ρ N hs⟩
  exact finiteIndex_action_representatives S hS hcover (N.comap ρ)
    (by rwa [Subgroup.index_comap_of_surjective _ hρ])

end CriticalPercolation.BondGraph
end
end
end

end OAI
