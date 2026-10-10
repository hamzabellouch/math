import OAI.Algebra.AuslanderReiten.Homology.ShortExactConnecting
import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleNaturality
import OAI.Algebra.AuslanderReiten.Complete.ProjectiveCompleteResolution

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (L M : FiniteLeftModule k R)

def resolutionSourceStableEquiv :
    CohomologyClass (L.completeCochain τ) (M.completeCochain τ) 1 ≃+
      StableHom R (RawSyzygy (L.completeCochain τ)) M.carrier :=
  (rawSourceStableEquiv (k := k) _ _
    (L.completeCochain_totallyAcyclic τ).to_chain
    (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).trans
      (StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ)).targetAddEquiv

variable {L M} {N : FiniteLeftModule k R}
variable (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)

theorem resolutionConnecting_source
    (A : (L.completeCochain τ).X 0 →ₗ[R] N.carrier)
    (t : RawSyzygy (L.completeCochain τ) →ₗ[R] M.carrier)
    (hA : g.comp A = (L.completeCochainCokernelEquiv τ).toLinearMap.comp
      (LinearMap.range ((L.completeCochain τ).d (-1) 0).hom).mkQ)
    (ht : f.comp t = A.comp (rawSyzygyInclusion (L.completeCochain τ))) :
    resolutionSourceStableEquiv τ L M
      ((fullHomShiftedHomotopyEquiv k (L.completeCochain τ) (M.completeCochain τ) 1).symm
        (resolutionConnecting τ f g hf hg hex)) = StableHom.classOf R _ _ t := by
  let := τ.regular_injective
  let A' := (N.completeCochainCokernelEquiv τ).symm.toLinearMap.comp A
  let t' := (M.completeCochainCokernelEquiv τ).symm.toLinearMap.comp t
  have hA' : (resolutionCokernelMap τ g).comp A' =
      (LinearMap.range ((L.completeCochain τ).d (-1) 0).hom).mkQ := by
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hA z
    simpa only [resolutionCokernelMap, A', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply] using
        congrArg (L.completeCochainCokernelEquiv τ).symm hz
  have ht' : (cochainCokernelMap (resolutionMap τ f)).comp t' =
      A'.comp (rawSyzygyInclusion (L.completeCochain τ)) := by
    rw [resolutionMap_cokernel]
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun ht z
    simpa only [resolutionCokernelMap, t', A', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        congrArg (N.completeCochainCokernelEquiv τ).symm hz
  change (StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ)).targetAddEquiv
    (rawSourceStableEquiv (k := k) _ _
      (L.completeCochain_totallyAcyclic τ).to_chain
      (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
      ((fullHomShiftedHomotopyEquiv k _ _ 1).symm
        (resolutionConnecting τ f g hf hg hex))) = _
  dsimp only [resolutionConnecting, resolutionTriangle]
  rw [shortExactConnecting_source_equiv (A := A') (t := t') (hA := hA') (ht := ht')]
  simp only [StableIsomorphism.targetAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  simp [t']

theorem projectiveMiddleShiftIso_source [Module.Projective R N.carrier]
    (A : (L.completeCochain τ).X 0 →ₗ[R] N.carrier)
    (t : RawSyzygy (L.completeCochain τ) →ₗ[R] M.carrier)
    (hA : g.comp A = (L.completeCochainCokernelEquiv τ).toLinearMap.comp
      (LinearMap.range ((L.completeCochain τ).d (-1) 0).hom).mkQ)
    (ht : f.comp t = A.comp (rawSyzygyInclusion (L.completeCochain τ))) :
    resolutionSourceStableEquiv τ L M
      ((fullHomShiftedHomotopyEquiv k (L.completeCochain τ) (M.completeCochain τ) 1).symm
        (projectiveMiddleShiftIso τ f g hf hg hex).hom) = StableHom.classOf R _ _ t :=
  resolutionConnecting_source τ f g hf hg hex A t hA ht

end ArExplicit.FiniteLeftModule

end

end OAI
