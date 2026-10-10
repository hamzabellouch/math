import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionIso

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

def resolutionHomotopyEquiv :
    ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ)) ≃+
    StableHom R M.carrier N.carrier :=
  (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).trans
      (((StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ).symm).sourceAddEquiv).trans
        ((StableIsomorphism.ofLinearEquiv (N.completeCochainCokernelEquiv τ)).targetAddEquiv))

@[simp] theorem resolutionHomotopyEquiv_map (f : M.carrier →ₗ[R] N.carrier) :
    resolutionHomotopyEquiv τ M N ((HomotopyCategory.quotient _ _).map (resolutionMap τ f)) =
      StableHom.classOf R _ _ f := by
  simp only [resolutionHomotopyEquiv, AddEquiv.trans_apply, cochainHomotopyRawEquiv_map,
    resolutionMap_cokernel, StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  congr 1
  ext x
  simp [resolutionCokernelMap]

variable {M N} {P : FiniteLeftModule k R}

theorem resolutionHomotopyEquiv_comp
    (f : (HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ))
    (g : (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj (P.completeCochain τ)) :
    resolutionHomotopyEquiv τ M P (f ≫ g) =
      StableHom.comp (resolutionHomotopyEquiv τ N P g) (resolutionHomotopyEquiv τ M N f) := by
  obtain ⟨f, rfl⟩ := resolutionMap_surjective τ f
  obtain ⟨g, rfl⟩ := resolutionMap_surjective τ g
  rw [← resolutionMap_comp, resolutionHomotopyEquiv_map, resolutionHomotopyEquiv_map,
    resolutionHomotopyEquiv_map, StableHom.comp_classOf]

@[simp] theorem resolutionHomotopyEquiv_id :
    resolutionHomotopyEquiv τ M M (𝟙 _) = StableHom.identity := by
  rw [← resolutionMap_id (M := M) τ, resolutionHomotopyEquiv_map]
  rfl

def stableResolutionIso (e : StableIsomorphism R M.carrier N.carrier) :
    (HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ≅
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) where
  hom := (resolutionHomotopyEquiv τ M N).symm e.hom
  inv := (resolutionHomotopyEquiv τ N M).symm e.inv
  hom_inv_id := by
    apply (resolutionHomotopyEquiv τ M M).injective
    rw [resolutionHomotopyEquiv_comp, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, resolutionHomotopyEquiv_id, e.hom_inv_id]
  inv_hom_id := by
    apply (resolutionHomotopyEquiv τ N N).injective
    rw [resolutionHomotopyEquiv_comp, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, resolutionHomotopyEquiv_id, e.inv_hom_id]

@[simp] theorem stableResolutionIso_hom (e : StableIsomorphism R M.carrier N.carrier) :
    resolutionHomotopyEquiv τ M N (stableResolutionIso τ e).hom = e.hom :=
  AddEquiv.apply_symm_apply _ _

theorem stableResolutionIso_hom_of_class (e : StableIsomorphism R M.carrier N.carrier)
    (f : M.carrier →ₗ[R] N.carrier) (hf : e.hom = StableHom.classOf R _ _ f) :
    (stableResolutionIso τ e).hom =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) := by
  apply (resolutionHomotopyEquiv τ M N).injective
  rw [stableResolutionIso_hom, hf, resolutionHomotopyEquiv_map]

end ArExplicit.FiniteLeftModule

end

end OAI
