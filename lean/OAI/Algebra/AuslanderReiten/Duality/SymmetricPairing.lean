import OAI.Algebra.AuslanderReiten.Duality.SymmetricHomology

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N] [SMulCommClass R k N]
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {r₁ r₀ rminus : ℕ}
variable (e : (Fin r₁ → R) →ₗ[R] (Fin r₀ → R))
variable (d : (Fin r₀ → R) →ₗ[R] (Fin rminus → R)) (h : d.comp e = 0)

theorem freeHomHomologyDuality_symm_apply
    (z : LinearMap.ker (StableTargetHomology.postcomp (k := k) (N := N) d))
    (x : LinearMap.ker (StableHomology.precomp (k := k) (N := N) e)) :
    ((τ.freeHomHomologyDuality hs e d h).symm
      (Submodule.Quotient.mk z)) (Submodule.Quotient.mk x) =
    (τ.freeHomDualEquiv r₀).symm z.val x.val := by
  simp only [freeHomHomologyDuality, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  rfl

theorem freeStableDuality_symm_cycles (hex : LinearMap.range e = LinearMap.ker d)
    (z : LinearMap.ker (StableTargetHomology.postcomp (k := k) (N := N) d))
    (x : LinearMap.ker (StableHomology.precomp (k := k) (N := N) e)) :
    ((τ.freeStableDuality (N := N) hs e d h hex).symm (StableTargetHomology.cyclesToStable d z))
      (StableHomology.cyclesToStable e x) =
    (τ.freeHomDualEquiv r₀).symm z.val x.val := by
  let : Module.Injective R R := τ.regular_injective
  let hd : HomExactAt e d := homExactAt_of_injective e d hex
  let qx : LinearHomology.Homology (StableHomology.precomp d)
    (StableHomology.precomp e) (StableHomology.precomp_comp e d h) := Submodule.Quotient.mk x
  let qz : LinearHomology.Homology (StableTargetHomology.postcomp e)
    (StableTargetHomology.postcomp d) (StableTargetHomology.postcomp_comp e d h) := Submodule.Quotient.mk z
  have hx : StableHomology.homologyStableEquiv e d h hd qx =
      StableHomology.cyclesToStable e x := StableHomology.homologyStableEquiv_mk e d h hd x
  have hz : StableTargetHomology.homologyStableEquiv e d h hex qz =
      StableTargetHomology.cyclesToStable d z :=
    StableTargetHomology.homologyStableEquiv_mk e d h hex z
  rw [← hx, ← hz]
  unfold freeStableDuality
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change ((τ.freeHomHomologyDuality hs e d h).symm qz)
    ((StableHomology.homologyStableEquiv e d h hd).symm
      ((StableHomology.homologyStableEquiv e d h hd) qx)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact τ.freeHomHomologyDuality_symm_apply hs e d h z x

theorem freeStableDuality_symm_apply (hex : LinearMap.range e = LinearMap.ker d)
    (f : StableHomology.Cokernel e →ₗ[R] N) (g : N →ₗ[R] LinearMap.ker d) :
    ((τ.freeStableDuality (N := N) hs e d h hex).symm (StableHom.classOf R _ _ g))
      (StableHom.classOf R _ _ f) =
    (τ.freeHomDualEquiv r₀).symm ((LinearMap.ker d).subtype.comp g)
      (f.comp (LinearMap.range e).mkQ) := by
  have H := τ.freeStableDuality_symm_cycles hs e d h hex
    (StableTargetHomology.mapToCycle d g) (StableHomology.mapToCycle e f)
  rw [StableTargetHomology.cyclesToStable_mapToCycle,
    StableHomology.cyclesToStable_mapToCycle] at H
  simpa only [StableTargetHomology.mapToCycle, StableHomology.mapToCycle] using H

variable {N' : Type u} [AddCommGroup N'] [Module R N'] [Module k N']
variable [IsScalarTower k R N'] [SMulCommClass R k N']

theorem freeStableDuality_natural (hex : LinearMap.range e = LinearMap.ker d)
    (u : N →ₗ[R] N') (f : StableHom R (StableHomology.Cokernel e) N)
    (g : StableHom R N' (LinearMap.ker d)) :
    ((τ.freeStableDuality hs e d h hex).symm g) (StableHom.postcomp u f) =
      ((τ.freeStableDuality hs e d h hex).symm (StableHom.precomp u g)) f := by
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective f
  obtain ⟨g, rfl⟩ := StableHom.classOf_surjective g
  rw [StableHom.postcomp_classOf, StableHom.precomp_classOf,
    τ.freeStableDuality_symm_apply hs e d h hex,
    τ.freeStableDuality_symm_apply hs e d h hex]
  exact τ.freeHomDual_naturality_target r₀ u (f.comp (LinearMap.range e).mkQ)
    ((LinearMap.ker d).subtype.comp g)

end ArExplicit.FrobeniusTrace

end OAI
