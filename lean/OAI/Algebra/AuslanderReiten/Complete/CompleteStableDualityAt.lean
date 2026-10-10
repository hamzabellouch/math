import OAI.Algebra.AuslanderReiten.Complete.CompleteStableSourceNaturality

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.FrobeniusTrace
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b) = τ.trace (b*a))
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
  [IsScalarTower k R N] [SMulCommClass R k N]
open CompleteComparison

def completeStableDualityAt (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hP : ExactProjectiveComplex P) (a : ℤ) :
    Module.Dual k (StableHom R (Cokernel P a) N) ≃ₗ[k]
      StableHom R N (Cokernel P (a+1)) := by
  letI := hP.finite (a+1)
  letI := hP.projective (a+1)
  letI := hP.finite a
  letI := hP.projective a
  letI := hP.finite (a-1)
  letI := hP.projective (a-1)
  exact (τ.projectiveStableDuality hs (P.d (a+1) a).hom (P.d a (a-1)).hom
    (differential_comp P (a+1) a (a-1)) (hP.exactAt a)).trans
      (StableHom.targetEquiv (k := k) (cokernelSyzygyEquiv hP a).symm)

theorem completeStableDualityAt_symm_apply
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : ExactProjectiveComplex P) (a : ℤ)
    (f : Cokernel P a →ₗ[R] N) (g : N →ₗ[R] Cokernel P (a+1)) :
    ((τ.completeStableDualityAt hs P hP a).symm (StableHom.classOf R _ _ g))
      (StableHom.classOf R _ _ f) =
    letI := hP.finite a
    letI := hP.projective a
    (τ.projectiveHomDualEquiv hs).symm ((syzygyInclusion hP a).comp g)
      (f.comp (LinearMap.range (P.d (a+1) a).hom).mkQ) := by
  let := hP.finite (a+1)
  let := hP.projective (a+1)
  let := hP.finite a
  let := hP.projective a
  let := hP.finite (a-1)
  let := hP.projective (a-1)
  change ((τ.projectiveStableDuality hs (P.d (a+1) a).hom (P.d a (a-1)).hom
    (differential_comp P (a+1) a (a-1)) (hP.exactAt a)).symm
      (StableHom.targetEquiv (k := k) (cokernelSyzygyEquiv hP a)
        (StableHom.classOf R _ _ g))) (StableHom.classOf R _ _ f) = _
  rw [StableHom.targetEquiv_classOf]
  exact τ.projectiveStableDuality_symm_apply hs (P.d (a+1) a).hom (P.d a (a-1)).hom
    (differential_comp P (a+1) a (a-1)) (hP.exactAt a) f
    ((cokernelSyzygyEquiv hP a).toLinearMap.comp g)

theorem completeStableDualityAt_source
    {P Q : ChainComplex (ModuleCat.{u} R) ℤ}
    (hP : ExactProjectiveComplex P) (hQ : ExactProjectiveComplex Q) (a b : ℤ)
    (t : P.X a →ₗ[R] Q.X b)
    (α : Cokernel P a →ₗ[R] Cokernel Q b)
    (β : Cokernel P (a+1) →ₗ[R] Cokernel Q (b+1))
    (hα : α.comp (LinearMap.range (P.d (a+1) a).hom).mkQ =
      (LinearMap.range (Q.d (b+1) b).hom).mkQ.comp t)
    (hβ : (syzygyInclusion hQ b).comp β = t.comp (syzygyInclusion hP a))
    (f : StableHom R (Cokernel Q b) N) (g : StableHom R N (Cokernel P (a+1))) :
    ((τ.completeStableDualityAt hs P hP a).symm g) (StableHom.precomp α f) =
      ((τ.completeStableDualityAt hs Q hQ b).symm (StableHom.postcomp β g)) f := by
  obtain ⟨f,rfl⟩ := StableHom.classOf_surjective f
  obtain ⟨g,rfl⟩ := StableHom.classOf_surjective g
  rw [StableHom.precomp_classOf, StableHom.postcomp_classOf,
    completeStableDualityAt_symm_apply, completeStableDualityAt_symm_apply]
  let := hP.finite a
  let := hP.projective a
  let := hQ.finite b
  let := hQ.projective b
  have hf : (f.comp α).comp (LinearMap.range (P.d (a+1) a).hom).mkQ =
      (f.comp (LinearMap.range (Q.d (b+1) b).hom).mkQ).comp t := by
    rw [LinearMap.comp_assoc, hα, ← LinearMap.comp_assoc]
  have hg : (syzygyInclusion hQ b).comp (β.comp g) =
      t.comp ((syzygyInclusion hP a).comp g) := by
    rw [← LinearMap.comp_assoc, hβ, LinearMap.comp_assoc]
  rw [hf, hg]
  exact τ.presentationHomDual_naturality_source hs
    (FiniteProjectivePresentation.choose R (P.X a))
    (FiniteProjectivePresentation.choose R (Q.X b)) t
    (f.comp (LinearMap.range (Q.d (b+1) b).hom).mkQ) ((syzygyInclusion hP a).comp g)

end ArExplicit.FrobeniusTrace

end

end OAI
