import OAI.Algebra.AuslanderReiten.Cones.CochainCokernelIso
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomHomotopyMaps

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
variable (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)

def cokernelCochainLift (p : CochainCokernel K →ₗ[R] CochainCokernel L) : K ⟶ L :=
  Classical.choose (cochainCokernelMap_surjective hK.to_chain
    hL.to_chain.toExactProjectiveComplex p)

@[simp] theorem cokernelCochainLift_map (p : CochainCokernel K →ₗ[R] CochainCokernel L) :
    cochainCokernelMap (cokernelCochainLift hK hL p) = p :=
  Classical.choose_spec (cochainCokernelMap_surjective hK.to_chain
    hL.to_chain.toExactProjectiveComplex p)

theorem cokernelCochainLift_quotient (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).map (cokernelCochainLift hK hL e.toLinearMap) =
      (rawCokernelHomotopyIso hK hL e).hom := by
  apply (cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cokernelCochainLift_map, rawCokernelHomotopyIso_hom]

theorem cokernelCochainLift_quotient_inv (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).map (cokernelCochainLift hL hK e.symm.toLinearMap) =
      (rawCokernelHomotopyIso hK hL e).inv := by
  apply (cochainHomotopyRawEquiv hL.to_chain hK.to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cokernelCochainLift_map]
  exact (AddEquiv.apply_symm_apply _ _).symm

theorem cokernelCochainLift_homotopy_inverse (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).map
      (cokernelCochainLift hK hL e.toLinearMap ≫ cokernelCochainLift hL hK e.symm.toLinearMap) = 𝟙 _ := by
  rw [CategoryTheory.Functor.map_comp, cokernelCochainLift_quotient,
    cokernelCochainLift_quotient_inv, Iso.hom_inv_id]

end ArExplicit.CompleteComparison

end

end OAI
