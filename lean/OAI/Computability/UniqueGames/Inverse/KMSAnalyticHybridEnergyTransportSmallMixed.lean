import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyTransportSmall
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedEnergyLemmas

namespace OAI

section

/-!
# Exact transport of mixed small-component slices

A codomain equivalence transports the fixed primal coordinates and the
prescribed partial frequency together. The frequency reindexing is bijective,
so the actual slice energy has no multiplicity or normalization factor.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment

variable {A I J F F' : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup F] [Module F2 F]
  [AddCommGroup F'] [Module F2 F']

/-- Transport of the fixed block and the free block commutes with the actual
partial restriction. -/
theorem partialRestrict_codomain_pullback (b : F ≃ₗ[F2] F')
    (g : ((A × I) →ₗ[F2] F') → ℝ) (u : A →ₗ[F2] F) :
    partialRestrict (fun Y => g (b.toLinearMap.comp Y)) u =
      fun X => partialRestrict g (b.toLinearMap.comp u) (b.toLinearMap.comp X) := by
  funext X
  change g (b.toLinearMap.comp (u.coprod X)) =
    g ((b.toLinearMap.comp u).coprod (b.toLinearMap.comp X))
  apply congrArg g
  apply LinearMap.ext
  intro p
  change b (u p.1 + X p.2) = b (u p.1) + b (X p.2)
  exact b.map_add _ _

private theorem arrowCongr_refl_left_apply (b : F ≃ₗ[F2] F') (X : I →ₗ[F2] F) :
    LinearEquiv.arrowCongr (LinearEquiv.refl F2 I) b X = b.toLinearMap.comp X := by
  ext x
  rfl

private theorem arrowCongr_refl_right_apply (b : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I) T =
      T.comp b.symm.toLinearMap := by
  ext x
  rfl

variable [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (F →ₗ[F2] I)] [Fintype (F' →ₗ[F2] I)] in
/-- Exact coefficient transport for a function pulled back only in its
primal codomain. -/
theorem linearCoeff_postcomp_equiv (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (fun X => g (b.toLinearMap.comp X)) T =
      linearCoeff g (T.comp b.symm.toLinearMap) := by
  simpa only [arrowCongr_refl_left_apply, arrowCongr_refl_right_apply] using
    NaturalTransport.linearCoeff_pullback (LinearEquiv.refl F2 I) b g T

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
/-- Transport the prescribed frequency with the codomain. This identity
requires no surjectivity of the prescribed-frequency projection. -/
theorem sliceEnergy_codomain_pullback (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) :
    sliceEnergy (fun T : F →ₗ[F2] I => π.comp T = ν)
      (fun X => g (b.toLinearMap.comp X)) =
      sliceEnergy (fun T : F' →ₗ[F2] I => π.comp T = ν.comp b.symm.toLinearMap) g := by
  unfold sliceEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv (LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I)).toEquiv
  intro T
  have hp : π.comp (T.comp b.symm.toLinearMap) = ν.comp b.symm.toLinearMap ↔
      π.comp T = ν := by
    constructor
    · intro h
      ext x
      have hx := congrArg (fun M : F' →ₗ[F2] J => M (b x)) h
      simpa using hx
    · intro h
      rw [← LinearMap.comp_assoc, h]
  simp only [LinearEquiv.coe_toEquiv, arrowCongr_refl_right_apply,
    linearCoeff_postcomp_equiv, hp]

variable {E E' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 A]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype ((A × I) →ₗ[F2] F')] [Fintype (F' →ₗ[F2] (A × I))]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in
/-- The actual mixed small-component energy is invariant when its ambient
coordinates, embedding, fixed primal map, and prescribed frequency are all
transported together. -/
theorem sliceEnergy_partialRestrict_smallComponent_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : (A × I) →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ)
    (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) (u : A →ₗ[F2] F) :
    sliceEnergy (fun T : F →ₗ[F2] I => π.comp T = ν)
      (partialRestrict (smallComponent ι
        (fun M => f (LinearEquiv.arrowCongr a b M))) u) =
      sliceEnergy (fun T : F' →ₗ[F2] I => π.comp T = ν.comp b.symm.toLinearMap)
        (partialRestrict (smallComponent (a.toLinearMap.comp ι) f)
          (b.toLinearMap.comp u)) := by
  rw [smallComponent_pullback, partialRestrict_codomain_pullback]
  exact sliceEnergy_codomain_pullback b _ π ν

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
