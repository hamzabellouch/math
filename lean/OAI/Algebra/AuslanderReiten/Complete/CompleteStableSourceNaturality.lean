import OAI.Algebra.AuslanderReiten.Duality.ProjectiveStablePairing

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

def syzygyInclusion (hP : ExactProjectiveComplex P) (n : ℤ) :
    Cokernel P (n+1) →ₗ[R] P.X n :=
  (LinearMap.ker (P.d n (n-1)).hom).subtype.comp (cokernelSyzygyEquiv hP n).toLinearMap

@[simp] theorem syzygyInclusion_mk (hP : ExactProjectiveComplex P) (n : ℤ)
    (x : P.X (n+1)) :
    syzygyInclusion hP n (Submodule.Quotient.mk x) = (P.d (n+1) n).hom x := rfl

theorem syzygyInclusion_natural (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (f : P ⟶ Q) (n : ℤ) :
    (syzygyInclusion hQ n).comp (cokernelMap f (n+1)) =
      (f.f n).hom.comp (syzygyInclusion hP n) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (Q.d (n+1) n).hom ((f.f (n+1)).hom x) =
      (f.f n).hom ((P.d (n+1) n).hom x)
    exact congrArg (fun v => v.hom x) (f.comm (n+1) n)

end ArExplicit.CompleteComparison

namespace ArExplicit.FrobeniusTrace
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b) = τ.trace (b*a))
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
  [IsScalarTower k R N] [SMulCommClass R k N]
open CompleteComparison

theorem completeStableDuality_symm_apply
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : ExactProjectiveComplex P)
    (f : Cokernel P 0 →ₗ[R] N) (g : N →ₗ[R] Cokernel P 1) :
    ((τ.completeStableDuality hs P hP).symm (StableHom.classOf R _ _ g))
      (StableHom.classOf R _ _ f) =
    letI := hP.finite 0
    letI := hP.projective 0
    (τ.projectiveHomDualEquiv hs).symm ((syzygyInclusion hP 0).comp g)
      (f.comp (LinearMap.range (P.d 1 0).hom).mkQ) := by
  let := hP.finite 1
  let := hP.projective 1
  let := hP.finite 0
  let := hP.projective 0
  let := hP.finite (-1)
  let := hP.projective (-1)
  change ((τ.projectiveStableDuality hs (P.d 1 0).hom (P.d 0 (-1)).hom
    (differential_comp P 1 0 (-1)) (hP.exactAt 0)).symm
      (StableHom.targetEquiv (k := k) (cokernelSyzygyEquiv hP 0)
        (StableHom.classOf R _ _ g))) (StableHom.classOf R _ _ f) = _
  rw [StableHom.targetEquiv_classOf]
  exact τ.projectiveStableDuality_symm_apply hs (P.d 1 0).hom (P.d 0 (-1)).hom
    (differential_comp P 1 0 (-1)) (hP.exactAt 0) f ((cokernelSyzygyEquiv hP 0).toLinearMap.comp g)

theorem completeStableDuality_natural_source
    {P Q : ChainComplex (ModuleCat.{u} R) ℤ}
    (hP : ExactProjectiveComplex P) (hQ : ExactProjectiveComplex Q) (u : P ⟶ Q)
    (f : StableHom R (Cokernel Q 0) N) (g : StableHom R N (Cokernel P 1)) :
    ((τ.completeStableDuality hs P hP).symm g) (StableHom.precomp (cokernelMap u 0) f) =
      ((τ.completeStableDuality hs Q hQ).symm (StableHom.postcomp (cokernelMap u 1) g)) f := by
  obtain ⟨f,rfl⟩ := StableHom.classOf_surjective f
  obtain ⟨g,rfl⟩ := StableHom.classOf_surjective g
  rw [StableHom.precomp_classOf, StableHom.postcomp_classOf,
    completeStableDuality_symm_apply, completeStableDuality_symm_apply]
  let := hP.finite 0
  let := hP.projective 0
  let := hQ.finite 0
  let := hQ.projective 0
  have hf : (f.comp (cokernelMap u 0)).comp (LinearMap.range (P.d 1 0).hom).mkQ =
      (f.comp (LinearMap.range (Q.d 1 0).hom).mkQ).comp (u.f 0).hom := rfl
  have hg : (syzygyInclusion hQ 0).comp ((cokernelMap u 1).comp g) =
      (u.f 0).hom.comp ((syzygyInclusion hP 0).comp g) := by
    exact congrArg (fun v => v.comp g) (syzygyInclusion_natural hP hQ u 0)
  rw [hf, hg]
  exact τ.presentationHomDual_naturality_source hs
    (FiniteProjectivePresentation.choose R (P.X 0))
    (FiniteProjectivePresentation.choose R (Q.X 0)) (u.f 0).hom
    (f.comp (LinearMap.range (Q.d 1 0).hom).mkQ) ((syzygyInclusion hP 0).comp g)

end ArExplicit.FrobeniusTrace

end

end OAI
