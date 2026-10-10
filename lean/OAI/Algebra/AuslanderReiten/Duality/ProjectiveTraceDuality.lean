import OAI.Algebra.AuslanderReiten.Duality.SymmetricHomology
import OAI.Algebra.AuslanderReiten.Homology.LinearRetractEquiv

namespace OAI

namespace ArExplicit

universe u

variable (R P : Type u) [Ring R] [AddCommGroup P] [Module R P]

structure FiniteProjectivePresentation where
  rank : ℕ
  inclusion : P →ₗ[R] (Fin rank → R)
  projection : (Fin rank → R) →ₗ[R] P
  split : projection.comp inclusion = LinearMap.id

namespace FiniteProjectivePresentation

noncomputable def choose [Module.Finite R P] [Module.Projective R P] :
    FiniteProjectivePresentation R P := by
  let h := Module.Finite.exists_fin' R P
  let hs := Module.projective_lifting_property h.choose_spec.choose
    (LinearMap.id : P →ₗ[R] P) h.choose_spec.choose_spec
  exact ⟨h.choose, hs.choose, h.choose_spec.choose, hs.choose_spec⟩

variable {R P}

@[simp]
theorem split_apply (F : FiniteProjectivePresentation R P) (x : P) :
    F.projection (F.inclusion x) = x := DFunLike.congr_fun F.split x

end FiniteProjectivePresentation

namespace FrobeniusTrace

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {P Q N : Type u}
variable [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]
variable [AddCommGroup Q] [Module R Q] [Module k Q] [IsScalarTower k R Q]
variable [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
variable [SMulCommClass R k N]

noncomputable def presentationHomDualEquiv (F : FiniteProjectivePresentation R P) :
    Module.Dual k (P →ₗ[R] N) ≃ₗ[k] (N →ₗ[R] P) :=
  linearRetractEquiv
    (StableHomology.precomp (k := k) F.inclusion).dualMap
    (StableHomology.precomp (k := k) F.projection).dualMap (by
      ext φ f
      change φ ((f.comp F.projection).comp F.inclusion) = φ f
      congr 1
      ext x
      exact congrArg f (F.split_apply x))
    (StableTargetHomology.postcomp (k := k) F.inclusion)
    (StableTargetHomology.postcomp (k := k) F.projection) (by
      ext g x
      exact F.split_apply (g x))
    (τ.freeHomDualEquiv F.rank) (by
      intro φ
      exact τ.freeHomDual_precomp hs (F.inclusion.comp F.projection) φ)

theorem presentationHomDualEquiv_symm_apply (F : FiniteProjectivePresentation R P)
    (g : N →ₗ[R] P) (f : P →ₗ[R] N) :
    (τ.presentationHomDualEquiv hs F).symm g f =
      (τ.freeHomDualEquiv F.rank).symm (F.inclusion.comp g) (f.comp F.projection) := rfl

theorem presentationHomDual_naturality_source
    (F : FiniteProjectivePresentation R P) (G : FiniteProjectivePresentation R Q)
    (a : P →ₗ[R] Q) (f : Q →ₗ[R] N) (g : N →ₗ[R] P) :
    (τ.presentationHomDualEquiv hs F).symm g (f.comp a) =
      (τ.presentationHomDualEquiv hs G).symm (a.comp g) f := by
  rw [presentationHomDualEquiv_symm_apply, presentationHomDualEquiv_symm_apply]
  let A := G.inclusion.comp (a.comp F.projection)
  have H := τ.freeHomDual_naturality_source hs A (f.comp G.projection) (F.inclusion.comp g)
  have hleft : (f.comp G.projection).comp A = (f.comp a).comp F.projection := by
    apply LinearMap.ext
    intro x
    exact congrArg f (G.split_apply (a (F.projection x)))
  have hright : A.comp (F.inclusion.comp g) = G.inclusion.comp (a.comp g) := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun p => G.inclusion (a p)) (F.split_apply (g x))
  rw [hleft, hright] at H
  exact H

noncomputable def projectiveHomDualEquiv [Module.Finite R P] [Module.Projective R P] :
    Module.Dual k (P →ₗ[R] N) ≃ₗ[k] (N →ₗ[R] P) :=
  τ.presentationHomDualEquiv hs (FiniteProjectivePresentation.choose R P)

theorem projectiveHomDual_precomp [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q] (a : P →ₗ[R] Q)
    (φ : Module.Dual k (P →ₗ[R] N)) :
    τ.projectiveHomDualEquiv hs ((StableHomology.precomp (k := k) a).dualMap φ) =
      a.comp (τ.projectiveHomDualEquiv hs φ) := by
  apply (τ.projectiveHomDualEquiv hs (P := Q) (N := N)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  ext f
  change φ (f.comp a) =
    (τ.presentationHomDualEquiv hs (FiniteProjectivePresentation.choose R Q)).symm
      (a.comp (τ.projectiveHomDualEquiv hs φ)) f
  rw [← τ.presentationHomDual_naturality_source hs
    (FiniteProjectivePresentation.choose R P)]
  exact (congrArg (fun ψ : Module.Dual k (P →ₗ[R] N) => ψ (f.comp a))
    ((τ.projectiveHomDualEquiv hs).symm_apply_apply φ)).symm

variable {N' : Type u} [AddCommGroup N'] [Module R N'] [Module k N']
variable [IsScalarTower k R N'] [SMulCommClass R k N']

theorem projectiveHomDual_naturality_target [Module.Finite R P] [Module.Projective R P]
    (u : N →ₗ[R] N') (f : P →ₗ[R] N) (g : N' →ₗ[R] P) :
    (τ.projectiveHomDualEquiv hs).symm g (u.comp f) =
      (τ.projectiveHomDualEquiv hs).symm (g.comp u) f := by
  let F := FiniteProjectivePresentation.choose R P
  change (τ.presentationHomDualEquiv hs F).symm g (u.comp f) =
    (τ.presentationHomDualEquiv hs F).symm (g.comp u) f
  rw [presentationHomDualEquiv_symm_apply, presentationHomDualEquiv_symm_apply]
  exact τ.freeHomDual_naturality_target F.rank u (f.comp F.projection) (F.inclusion.comp g)

end FrobeniusTrace
end ArExplicit

end OAI
