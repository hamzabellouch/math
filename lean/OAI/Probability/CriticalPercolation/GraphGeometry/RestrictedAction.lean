import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphActionCoordinates
import OAI.Probability.CriticalPercolation.GraphGeometry.InducedAutomorphism

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

def domainPreserver (C : Set V) : Subgroup Λ where
  carrier := {g | ∀ x, g • x∈C ↔ x∈C}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg x
    simpa only [smul_inv_smul] using (hg (g⁻¹ • x)).symm

@[instance_reducible] def restrictedVertexAction (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L C where
  smul g x := ⟨(g : Λ) • x.val,(hL g.property x.val).mpr x.property⟩
  one_smul x := Subtype.ext (one_smul Λ x.val)
  mul_smul g h x := Subtype.ext (mul_smul (g : Λ) (h : Λ) x.val)

@[instance_reducible] def restrictedEdgeAction (ha : G.PreservesEnds (Λ := Λ))
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L (G.inducedEdges C) where
  smul g e := ⟨(g : Λ) • e.val,
    (Aut.inducedEdges_mem G (G.smulAut ha g.val) C (hL g.property) e.val).mpr e.property⟩
  one_smul e := Subtype.ext (one_smul Λ e.val)
  mul_smul g h e := Subtype.ext (mul_smul (g : Λ) (h : Λ) e.val)

lemma restricted_preservesEnds (ha : G.PreservesEnds (Λ := Λ))
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    let _ := G.restrictedEdgeAction ha C L hL
    (G.induce C).PreservesEnds (Λ := L) := by
  intro _ _ g e
  exact (Aut.restrict G (G.smulAut ha g.val) C (hL g.property)).preserves e

lemma restricted_kernel_orbits {N : Type*} [Group N]
    (ρ : Λ →* N) (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    ∀ v : C, (MulAction.orbit (ρ.comp L.subtype).ker v).Finite := by
  intro _ v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hker v.val)).subset
  rintro w ⟨g,hg⟩
  refine ⟨⟨(g.val : Λ),g.property⟩,?_⟩
  exact congrArg Subtype.val hg

lemma restricted_stabilizer_images {N : Type*} [Group N]
    (ρ : Λ →* N)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    ∀ v : C, ((MulAction.stabilizer L v).map (ρ.comp L.subtype) : Set N).Finite := by
  intro _ v
  apply (hstab v.val).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g.val,congrArg Subtype.val hg,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
