import OAI.GroupTheory.PolycyclicRecognition.Geometry.SpectralLieDerivation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SpectralLogExponential

namespace OAI

/-! # A finite power of a semisimple Lie automorphism has a derivation logarithm

The logarithm uses one additive character on the generated spectral group,
so the derivative respects every bracket relation.
-/

noncomputable section
namespace PolycyclicRecognition

/-- The analytic and Lie structures share their additive and scalar data. -/
class ComplexNormedLieAlgebra (L : Type*) extends NormedAddCommGroup L, LieRing L,
    NormedSpace ℂ L, LieAlgebra ℂ L

variable {L : Type} [ComplexNormedLieAlgebra L] [FiniteDimensional ℂ L] [CompleteSpace L]

theorem semisimple_lie_automorphism_has_power_log (S : L ≃ₗ⁅ℂ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℂ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m := by
  obtain ⟨m, hm, l, he, _⟩ := spectralUnitGroup_logarithm S.toLinearMap
  refine ⟨m, hm, spectralLieDerivation S hS l, ?_⟩
  exact exp_compatibleSpectralLog S.toLinearMap hS
    ((Module.End.isUnit_iff _).mpr S.bijective) l m he

theorem semisimple_real_form_has_commuting_power_log (S : L ≃ₗ⁅ℂ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (c : L →ₗ⋆[ℂ] L) (hc : ∀ x, c (S x) = S (c x)) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℂ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m ∧ (∀ x, c (D x) = D (c x)) ∧
        ∀ T : Module.End ℂ L, Commute S.toLinearMap T → Commute D.toLinearMap T := by
  obtain ⟨m, hm, l, he, hr⟩ := spectralUnitGroup_logarithm S.toLinearMap
  refine ⟨m, hm, spectralLieDerivation S hS l, ?_, ?_, ?_⟩
  · exact exp_compatibleSpectralLog S.toLinearMap hS
      ((Module.End.isUnit_iff _).mpr S.bijective) l m he
  · exact compatibleSpectralLog_conjugation S.toLinearMap hS l hr c hc
  · intro T hT
    exact semisimpleSpectralOperator_commute S.toLinearMap hS _ T hT

theorem semisimple_real_form_has_power_log (S : L ≃ₗ⁅ℂ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (c : L →ₗ⋆[ℂ] L) (hc : ∀ x, c (S x) = S (c x)) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℂ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m ∧ ∀ x, c (D x) = D (c x) := by
  obtain ⟨m, hm, D, he, hc, _⟩ := semisimple_real_form_has_commuting_power_log S hS c hc
  exact ⟨m, hm, D, he, hc⟩

end PolycyclicRecognition

end

end OAI
