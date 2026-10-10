import Mathlib

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

@[instance_reducible] def subspaceAction (ρ : G →* (V ≃ₗ[K] V)) : MulAction G (Submodule K V) where
  smul g W := W.map (ρ g).toLinearMap
  one_smul W := by
    change W.map (ρ 1).toLinearMap=W
    rw [map_one]
    exact W.map_id
  mul_smul g h W := by
    change W.map (ρ (g*h)).toLinearMap=(W.map (ρ h).toLinearMap).map (ρ g).toLinearMap
    rw [map_mul]
    exact (Submodule.map_comp _ _ W)

lemma finiteIndex_subspace_stabilizer (ρ : G →* (V ≃ₗ[K] V))
    (W : Submodule K V)
    (hf : (Set.range (fun g => W.map (ρ g).toLinearMap)).Finite) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∀ h : H, W.map (ρ h).toLinearMap=W := by
  let := subspaceAction ρ
  let H := MulAction.stabilizer G W
  have horb : (MulAction.orbit G W).Finite := hf
  let : Finite (MulAction.orbit G W) := horb.to_subtype
  let : Finite (G ⧸ H) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G W)
  refine ⟨H,Subgroup.finiteIndex_of_finite_quotient,?_⟩
  intro h
  exact h.property

end CriticalPercolation.LinearGrowth
end
end

end OAI
