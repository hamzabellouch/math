import OAI.Algebra.AuslanderReiten.Duality.ProjectiveTraceDuality
import OAI.Algebra.AuslanderReiten.Cones.CokernelSyzygy
import OAI.Algebra.AuslanderReiten.Stable.StableHomEquiv
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomLinear

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [Module k P₁] [IsScalarTower k R P₁]
variable [AddCommGroup P₀] [Module R P₀] [Module k P₀] [IsScalarTower k R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [Module k Pminus] [IsScalarTower k R Pminus]
variable [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
variable [SMulCommClass R k N]
variable [Module.Finite R P₁] [Module.Projective R P₁]
variable [Module.Finite R P₀] [Module.Projective R P₀]
variable [Module.Finite R Pminus] [Module.Projective R Pminus]

noncomputable def projectiveHomHomologyDuality
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0) :
    Module.Dual k (LinearHomology.Homology
      (StableHomology.precomp (k := k) (N := N) d)
      (StableHomology.precomp e) (StableHomology.precomp_comp e d h)) ≃ₗ[k]
    LinearHomology.Homology
      (StableTargetHomology.postcomp (k := k) (N := N) e)
      (StableTargetHomology.postcomp d) (StableTargetHomology.postcomp_comp e d h) :=
  (LinearHomology.dualHomologyEquiv _ _ _).trans
    (LinearHomology.congr _ _ _ _ _ _
      (τ.projectiveHomDualEquiv hs) (τ.projectiveHomDualEquiv hs) (τ.projectiveHomDualEquiv hs)
      (τ.projectiveHomDual_precomp hs e) (τ.projectiveHomDual_precomp hs d))

noncomputable def projectiveStableDuality
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d) :
    Module.Dual k (StableHom R (StableHomology.Cokernel e) N) ≃ₗ[k]
      StableHom R N (LinearMap.ker d) := by
  letI : Module.Injective R R := τ.regular_injective
  let hd : HomExactAt e d := homExactAt_of_injective e d hex
  exact (StableHomology.homologyStableEquiv e d h hd).dualMap |>.trans
    ((τ.projectiveHomHomologyDuality hs e d h).trans
      (StableTargetHomology.homologyStableEquiv e d h hex))

open scoped ModuleCat.Algebra
open CompleteComparison

noncomputable def completeStableDuality
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : ExactProjectiveComplex P) :
    Module.Dual k (StableHom R (Cokernel P 0) N) ≃ₗ[k]
      StableHom R N (Cokernel P 1) := by
  letI : ∀ i, Module.Finite R (P.X i) := hP.finite
  letI : ∀ i, Module.Projective R (P.X i) := hP.projective
  exact (τ.projectiveStableDuality hs (P.d 1 0).hom (P.d 0 (-1)).hom
    (differential_comp P 1 0 (-1)) (hP.exactAt 0)).trans
      (StableHom.targetEquiv (k := k) (cokernelSyzygyEquiv hP 0).symm)

end ArExplicit.FrobeniusTrace

end OAI
