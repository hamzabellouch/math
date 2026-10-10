import OAI.Algebra.AuslanderReiten.Coordinates.FiniteConnectingCoordinates
import OAI.Algebra.AuslanderReiten.Homology.ShortExactConnectingProducts
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComposition
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomDegreeProducts

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]
variable (τ : FrobeniusTrace k R)

def resolutionSourceAtStableEquiv (S M : FiniteLeftModule k R) (n : ℤ) :
    CohomologyClass (S.completeCochain τ) (M.completeCochain τ) n ≃+
      StableHom R (RawCokernelAt (S.completeCochain τ) n) M.carrier :=
  (rawSourceAtStableEquiv (k := k) _ _ n
    (S.completeCochain_totallyAcyclic τ).to_chain
    (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).trans
      (StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ)).targetAddEquiv

omit [CharP k 2] in
@[simp]
theorem resolutionSourceAtStableEquiv_mk (S M : FiniteLeftModule k R) (n : ℤ)
    (x : Cocycle (S.completeCochain τ) (M.completeCochain τ) n) :
    resolutionSourceAtStableEquiv τ S M n (CohomologyClass.mk x) =
      StableHom.classOf R _ _ ((M.completeCochainCokernelEquiv τ).toLinearMap.comp (rawSourceAt x)) := by
  simp only [resolutionSourceAtStableEquiv, AddEquiv.trans_apply, rawSourceAtStableEquiv_mk,
    StableIsomorphism.targetAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]

theorem resolutionSourceAtStableEquiv_postcomp (S M N : FiniteLeftModule k R)
    (n : ℤ) (f : M.carrier →ₗ[R] N.carrier)
    (u : CohomologyClass (S.completeCochain τ) (M.completeCochain τ) n) :
    resolutionSourceAtStableEquiv τ S N n (fullHomPostcomp (resolutionMap τ f) n u) =
      StableHom.postcomp f (resolutionSourceAtStableEquiv τ S M n u) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective u
  rw [fullHomPostcomp_mk, resolutionSourceAtStableEquiv_mk,
    resolutionSourceAtStableEquiv_mk, StableHom.postcomp_classOf,
    rawSourceAt_postcomp (k := k), resolutionMap_cokernel]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  simp [resolutionCokernelMap]

theorem resolutionSourceAtStableEquiv_identity (S : FiniteLeftModule k R) :
    resolutionSourceAtStableEquiv τ S S 0 (fullHomIdentity (S.completeCochain τ)) =
      StableHom.classOf R _ _ (S.completeCochainCokernelEquiv τ).toLinearMap := by
  rw [fullHomIdentity, resolutionSourceAtStableEquiv_mk]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((S.completeCochain τ).d (-1) 0).hom) z
  simp only [LinearMap.comp_apply]
  erw [rawSourceAt_mk (k := k)]
  rfl

variable {S L M N : FiniteLeftModule k R}
variable (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)

theorem resolutionConnecting_product_source (n : ℤ)
    (u : CohomologyClass (S.completeCochain τ) (L.completeCochain τ) n)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] L.carrier)
    (hs : resolutionSourceAtStableEquiv τ S L n u = StableHom.classOf R _ _ s)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier)
    (t : RawCokernelAt (S.completeCochain τ) (n+1) →ₗ[R] M.carrier)
    (hA : g.comp A = s.comp (LinearMap.range ((S.completeCochain τ).d (-(n+1)) (-n)).hom).mkQ)
    (ht : f.comp t = A.comp (rawCokernelAtInclusion (S.completeCochain τ) n)) :
    resolutionSourceAtStableEquiv τ S M (n+1)
      (fullHomProduct u
        ((fullHomShiftedHomotopyEquiv k (L.completeCochain τ) (M.completeCochain τ) 1).symm
          (resolutionConnecting τ f g hf hg hex))) = StableHom.classOf R _ _ t := by
  let := τ.regular_injective
  let s' := (L.completeCochainCokernelEquiv τ).symm.toLinearMap.comp s
  let A' := (N.completeCochainCokernelEquiv τ).symm.toLinearMap.comp A
  let t' := (M.completeCochainCokernelEquiv τ).symm.toLinearMap.comp t
  have hs' : rawSourceAtStableEquiv (k := k) _ _ n
      (S.completeCochain_totallyAcyclic τ).to_chain
      (L.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex u =
        StableHom.classOf R _ _ s' := by
    apply (StableIsomorphism.ofLinearEquiv (L.completeCochainCokernelEquiv τ)).targetAddEquiv.injective
    change resolutionSourceAtStableEquiv τ S L n u = _
    rw [hs]
    simp only [StableIsomorphism.targetAddEquiv, StableIsomorphism.ofLinearEquiv,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
    apply congrArg (StableHom.classOf R _ _)
    apply LinearMap.ext
    intro z
    simp [s']
  have hA' : (resolutionCokernelMap τ g).comp A' =
      s'.comp (LinearMap.range ((S.completeCochain τ).d (-(n+1)) (-n)).hom).mkQ := by
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hA z
    simpa only [resolutionCokernelMap, A', s', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        congrArg (L.completeCochainCokernelEquiv τ).symm hz
  have ht' : (cochainCokernelMap (resolutionMap τ f)).comp t' =
      A'.comp (rawCokernelAtInclusion (S.completeCochain τ) n) := by
    rw [resolutionMap_cokernel]
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun ht z
    simpa only [resolutionCokernelMap, t', A', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        congrArg (N.completeCochainCokernelEquiv τ).symm hz
  change (StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ)).targetAddEquiv
    (rawSourceAtStableEquiv (k := k) _ _ (n+1)
      (S.completeCochain_totallyAcyclic τ).to_chain
      (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex _) = _
  dsimp only [resolutionConnecting, resolutionTriangle]
  rw [shortExactConnecting_product_source
    (hK := S.completeCochain_totallyAcyclic τ) (s := s') (hs := hs')
    (A := A') (t := t') (hA := hA') (ht := ht')]
  simp only [StableIsomorphism.targetAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  simp [t']

end ArExplicit.FiniteLeftModule

end

end OAI
