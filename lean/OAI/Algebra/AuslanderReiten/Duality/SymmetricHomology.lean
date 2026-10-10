import OAI.Algebra.AuslanderReiten.Duality.SymmetricStableDuality
import OAI.Algebra.AuslanderReiten.Stable.StableTargetHomology
import OAI.Algebra.AuslanderReiten.Homology.LinearHomologyCongr
import OAI.Algebra.AuslanderReiten.Complete.SelfInjectiveComplex

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N] [SMulCommClass R k N]
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))

include hs in

theorem freeHomDual_precomp {r s : ℕ} (a : (Fin r → R) →ₗ[R] (Fin s → R))
    (φ : Module.Dual k ((Fin r → R) →ₗ[R] N)) :
    τ.freeHomDualEquiv s ((StableHomology.precomp (k := k) a).dualMap φ) =
      a.comp (τ.freeHomDualEquiv r φ) := by
  apply (τ.freeHomDualEquiv s).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  ext f
  change φ (f.comp a) = (τ.freeHomDualEquiv s).symm (a.comp (τ.freeHomDualEquiv r φ)) f
  rw [← τ.freeHomDual_naturality_source hs]
  rw [LinearEquiv.symm_apply_apply]

noncomputable def freeHomHomologyDuality {r₁ r₀ rminus : ℕ}
    (e : (Fin r₁ → R) →ₗ[R] (Fin r₀ → R))
    (d : (Fin r₀ → R) →ₗ[R] (Fin rminus → R)) (h : d.comp e = 0) :
    Module.Dual k (LinearHomology.Homology
      (StableHomology.precomp (k := k) (N := N) d)
      (StableHomology.precomp e) (StableHomology.precomp_comp e d h)) ≃ₗ[k]
    LinearHomology.Homology
      (StableTargetHomology.postcomp (k := k) (N := N) e)
      (StableTargetHomology.postcomp d) (StableTargetHomology.postcomp_comp e d h) :=
  (LinearHomology.dualHomologyEquiv _ _ _).trans
    (LinearHomology.congr _ _ _ _ _ _
      (τ.freeHomDualEquiv r₁) (τ.freeHomDualEquiv r₀) (τ.freeHomDualEquiv rminus)
      (τ.freeHomDual_precomp hs e) (τ.freeHomDual_precomp hs d))

noncomputable def freeStableDuality {r₁ r₀ rminus : ℕ}
    (e : (Fin r₁ → R) →ₗ[R] (Fin r₀ → R))
    (d : (Fin r₀ → R) →ₗ[R] (Fin rminus → R)) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d) :
    Module.Dual k (StableHom R (StableHomology.Cokernel e) N) ≃ₗ[k]
      StableHom R N (LinearMap.ker d) := by
  letI : Module.Injective R R := τ.regular_injective
  let hd : HomExactAt e d := homExactAt_of_injective e d hex
  exact (StableHomology.homologyStableEquiv e d h hd).dualMap |>.trans
    ((τ.freeHomHomologyDuality hs e d h).trans
      (StableTargetHomology.homologyStableEquiv e d h hex))

end ArExplicit.FrobeniusTrace

end OAI
