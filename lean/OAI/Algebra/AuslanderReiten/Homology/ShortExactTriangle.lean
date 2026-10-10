import OAI.Algebra.AuslanderReiten.Cones.MappingConeCokernel
import OAI.Algebra.AuslanderReiten.Coordinates.CochainStableComparison
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex

namespace ArExplicit

open CompleteComparison

universe u

variable {R : Type u} [Ring R] [Module.Injective R R]
variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (hex : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G)
variable (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

def shortExactConeIso :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj (mappingCone φ) ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj H :=
  stableCochainHomotopyIso (mappingCone_totallyAcyclic φ hF hG).to_chain hH.to_chain
    ((mappingConeStableQuotient φ p hex hF.toExactProjectiveCochain hi hp).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv H).symm))

def shortExactTriangle : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  Triangle.mk ((HomotopyCategory.quotient _ _).map φ)
    ((HomotopyCategory.quotient _ _).map (mappingCone.inr φ) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).hom)
    ((shortExactConeIso φ p hex hF hG hH hi hp).inv ≫ (mappingCone.triangleh φ).mor₃)

theorem shortExactTriangle_distinguished :
    shortExactTriangle φ p hex hF hG hH hi hp ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  apply isomorphic_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished φ)
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (shortExactConeIso φ p hex hF hG hH hi hp).symm ?_ ?_ ?_
  · change ((HomotopyCategory.quotient _ _).map φ) ≫ 𝟙 _ =
      𝟙 _ ≫ ((HomotopyCategory.quotient _ _).map φ)
    simp only [Category.comp_id, Category.id_comp]
  · change (((HomotopyCategory.quotient _ _).map (mappingCone.inr φ)) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).hom) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).inv =
      𝟙 _ ≫ ((HomotopyCategory.quotient _ _).map (mappingCone.inr φ))
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · change ((shortExactConeIso φ p hex hF hG hH hi hp).inv ≫ (mappingCone.triangleh φ).mor₃) ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map (𝟙 _) = _
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

theorem shortExactConeIso_hom :
    cochainHomotopyCokernelEquiv (mappingCone_totallyAcyclic φ hF hG).to_chain
      hH.to_chain.toExactProjectiveComplex (shortExactConeIso φ p hex hF hG hH hi hp).hom =
    StableHom.classOf R _ _ ((cochainCokernelLinearEquiv H).symm.toLinearMap.comp
      (completeConeQuotient φ p hex)) := by
  unfold shortExactConeIso
  rw [stableCochainHomotopyIso_hom]
  change StableHom.comp
    (StableHom.classOf R _ _ (cochainCokernelLinearEquiv H).symm.toLinearMap)
    (mappingConeStableQuotient φ p hex hF.toExactProjectiveCochain hi hp).hom = _
  rw [mappingConeStableQuotient_hom φ p hex hF.toExactProjectiveCochain hi hp,
    StableHom.comp_classOf]

theorem shortExactTriangle_second (ψ : G ⟶ H) (hψ : cochainCokernelMap ψ = p) :
    (shortExactTriangle φ p hex hF hG hH hi hp).mor₂ =
      (HomotopyCategory.quotient _ _).map ψ := by
  apply (cochainHomotopyCokernelEquiv hG.to_chain hH.to_chain.toExactProjectiveComplex).injective
  change cochainHomotopyCokernelEquiv hG.to_chain hH.to_chain.toExactProjectiveComplex
    (((HomotopyCategory.quotient _ _).map (mappingCone.inr φ)) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).hom) = _
  rw [cochainHomotopyCokernelEquiv_comp hG.to_chain
    (mappingCone_totallyAcyclic φ hF hG).to_chain hH.to_chain.toExactProjectiveComplex,
    shortExactConeIso_hom, cochainHomotopyCokernelEquiv_map, cochainHomotopyCokernelEquiv_map,
    StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  rw [LinearMap.comp_assoc, completeConeQuotient_inr]
  apply LinearMap.ext
  intro x
  apply (cochainCokernelLinearEquiv H).injective
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural ψ) x
  rw [hψ] at h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h.symm

include hex hF hG hH hi hp in

theorem exists_shortExact_distinguished (ψ : G ⟶ H) (hψ : cochainCokernelMap ψ = p) :
    ∃ δ : (HomotopyCategory.quotient _ _).obj H ⟶
        ((HomotopyCategory.quotient _ _).obj F)⟦(1 : ℤ)⟧,
      Triangle.mk ((HomotopyCategory.quotient _ _).map φ)
        ((HomotopyCategory.quotient _ _).map ψ) δ ∈
        distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  refine ⟨(shortExactTriangle φ p hex hF hG hH hi hp).mor₃, ?_⟩
  have ht := shortExactTriangle_distinguished φ p hex hF hG hH hi hp
  have he := shortExactTriangle_second φ p hex hF hG hH hi hp ψ hψ
  change (Triangle.mk _ _ _) ∈ _ at ht
  rw [← he]
  exact ht

end ArExplicit

end

end OAI
