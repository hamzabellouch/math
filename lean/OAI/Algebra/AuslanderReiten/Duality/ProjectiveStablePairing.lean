import OAI.Algebra.AuslanderReiten.Duality.ProjectiveStableDuality

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N] [SMulCommClass R k N]
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {P₁ P₀ Pminus : Type u}
variable [AddCommGroup P₁] [Module R P₁] [Module k P₁] [IsScalarTower k R P₁]
variable [AddCommGroup P₀] [Module R P₀] [Module k P₀] [IsScalarTower k R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [Module k Pminus] [IsScalarTower k R Pminus]
variable [Module.Finite R P₁] [Module.Projective R P₁]
variable [Module.Finite R P₀] [Module.Projective R P₀]
variable [Module.Finite R Pminus] [Module.Projective R Pminus]
variable (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)

theorem projectiveHomHomologyDuality_symm_apply
    (z : LinearMap.ker (StableTargetHomology.postcomp (k := k) (N := N) d))
    (x : LinearMap.ker (StableHomology.precomp (k := k) (N := N) e)) :
    ((τ.projectiveHomHomologyDuality hs e d h).symm
      (Submodule.Quotient.mk z)) (Submodule.Quotient.mk x) =
    (τ.projectiveHomDualEquiv hs).symm z.val x.val := by
  simp only [projectiveHomHomologyDuality, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  rfl

theorem projectiveStableDuality_symm_cycles (hex : LinearMap.range e = LinearMap.ker d)
    (z : LinearMap.ker (StableTargetHomology.postcomp (k := k) (N := N) d))
    (x : LinearMap.ker (StableHomology.precomp (k := k) (N := N) e)) :
    ((τ.projectiveStableDuality (N := N) hs e d h hex).symm (StableTargetHomology.cyclesToStable d z))
      (StableHomology.cyclesToStable e x) =
    (τ.projectiveHomDualEquiv hs).symm z.val x.val := by
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
  unfold projectiveStableDuality
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change ((τ.projectiveHomHomologyDuality hs e d h).symm qz)
    ((StableHomology.homologyStableEquiv e d h hd).symm
      ((StableHomology.homologyStableEquiv e d h hd) qx)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact τ.projectiveHomHomologyDuality_symm_apply hs e d h z x

theorem projectiveStableDuality_symm_apply (hex : LinearMap.range e = LinearMap.ker d)
    (f : StableHomology.Cokernel e →ₗ[R] N) (g : N →ₗ[R] LinearMap.ker d) :
    ((τ.projectiveStableDuality (N := N) hs e d h hex).symm (StableHom.classOf R _ _ g))
      (StableHom.classOf R _ _ f) =
    (τ.projectiveHomDualEquiv hs).symm ((LinearMap.ker d).subtype.comp g)
      (f.comp (LinearMap.range e).mkQ) := by
  have H := τ.projectiveStableDuality_symm_cycles hs e d h hex
    (StableTargetHomology.mapToCycle d g) (StableHomology.mapToCycle e f)
  rw [StableTargetHomology.cyclesToStable_mapToCycle,
    StableHomology.cyclesToStable_mapToCycle] at H
  simpa only [StableTargetHomology.mapToCycle, StableHomology.mapToCycle] using H

variable {N' : Type u} [AddCommGroup N'] [Module R N'] [Module k N']
variable [IsScalarTower k R N'] [SMulCommClass R k N']

theorem projectiveStableDuality_natural (hex : LinearMap.range e = LinearMap.ker d)
    (u : N →ₗ[R] N') (f : StableHom R (StableHomology.Cokernel e) N)
    (g : StableHom R N' (LinearMap.ker d)) :
    ((τ.projectiveStableDuality hs e d h hex).symm g) (StableHom.postcomp u f) =
      ((τ.projectiveStableDuality hs e d h hex).symm (StableHom.precomp u g)) f := by
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective f
  obtain ⟨g, rfl⟩ := StableHom.classOf_surjective g
  rw [StableHom.postcomp_classOf, StableHom.precomp_classOf,
    τ.projectiveStableDuality_symm_apply hs e d h hex,
    τ.projectiveStableDuality_symm_apply hs e d h hex]
  exact τ.projectiveHomDual_naturality_target hs u (f.comp (LinearMap.range e).mkQ)
    ((LinearMap.ker d).subtype.comp g)

end ArExplicit.FrobeniusTrace

end OAI
