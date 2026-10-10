import OAI.Algebra.AuslanderReiten.Homology.ShortExactNaturality

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
universe u
variable {R : Type u} [Ring R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

theorem rawEquiv_identity (hK : TotallyAcyclicCochain K) :
    cochainHomotopyRawEquiv hK.to_chain hK.to_chain.toExactProjectiveComplex (𝟙 _) =
      StableHom.identity := by
  rw [← (HomotopyCategory.quotient _ _).map_id, cochainHomotopyRawEquiv_map]
  congr 1
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (K.d (-1) 0).hom) z
  rfl

def rawCokernelHomotopyIso (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).obj K ≅ (HomotopyCategory.quotient _ _).obj L where
  hom := (cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex).symm
    (StableHom.classOf R _ _ e.toLinearMap)
  inv := (cochainHomotopyRawEquiv hL.to_chain hK.to_chain.toExactProjectiveComplex).symm
    (StableHom.classOf R _ _ e.symm.toLinearMap)
  hom_inv_id := by
    apply (cochainHomotopyRawEquiv hK.to_chain hK.to_chain.toExactProjectiveComplex).injective
    rw [cochainHomotopyRawEquiv_comp hK hL hK.toExactProjectiveCochain,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, StableHom.comp_classOf,
      rawEquiv_identity hK]
    exact congrArg (StableHom.classOf R _ _) e.symm_comp
  inv_hom_id := by
    apply (cochainHomotopyRawEquiv hL.to_chain hL.to_chain.toExactProjectiveComplex).injective
    rw [cochainHomotopyRawEquiv_comp hL hK hL.toExactProjectiveCochain,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, StableHom.comp_classOf,
      rawEquiv_identity hL]
    exact congrArg (StableHom.classOf R _ _) e.comp_symm

@[simp] theorem rawCokernelHomotopyIso_hom
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex
      (rawCokernelHomotopyIso hK hL e).hom = StableHom.classOf R _ _ e.toLinearMap :=
  AddEquiv.apply_symm_apply _ _

variable {K' L' : CochainComplex (ModuleCat.{u} R) ℤ}

theorem rawCokernelHomotopyIso_natural
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (hK' : TotallyAcyclicCochain K') (hL' : TotallyAcyclicCochain L')
    (e : CochainCokernel K ≃ₗ[R] CochainCokernel L)
    (e' : CochainCokernel K' ≃ₗ[R] CochainCokernel L')
    (a : K ⟶ K') (b : L ⟶ L')
    (hab : e'.toLinearMap.comp (cochainCokernelMap a) =
      (cochainCokernelMap b).comp e.toLinearMap) :
    (HomotopyCategory.quotient _ _).map a ≫ (rawCokernelHomotopyIso hK' hL' e').hom =
      (rawCokernelHomotopyIso hK hL e).hom ≫ (HomotopyCategory.quotient _ _).map b := by
  apply (cochainHomotopyRawEquiv hK.to_chain hL'.to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_comp hK hK' hL'.toExactProjectiveCochain,
    cochainHomotopyRawEquiv_comp hK hL hL'.toExactProjectiveCochain,
    cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    rawCokernelHomotopyIso_hom, rawCokernelHomotopyIso_hom,
    StableHom.comp_classOf, StableHom.comp_classOf, hab]

end ArExplicit.CompleteComparison

end

end OAI
