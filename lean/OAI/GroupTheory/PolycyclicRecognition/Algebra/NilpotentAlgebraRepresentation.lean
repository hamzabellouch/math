import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnitsLieAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentModelIntegration

namespace OAI

/-! # Integrating nilpotent factor representations into matrix units

The source model is arbitrary and the represented matrices need not be
nilpotent. Only the source Lie algebra is nilpotent.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

theorem NilpotentLieModel.exists_algebra_representation
    {L A : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (N : NilpotentLieModel L) (hn : LieRing.IsNilpotent L) (j : L →ₗ⁅ℝ⁆ A) :
    ∃ ρ : N.carrier →* Aˣ,
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, A)) ∞ ρ ∧
      ∀ (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
        IsGroupExponential ExpN → ∀ x : L,
          ρ (ExpN (N.equiv x)) = algebraExpUnit (j x) := by
  let f := (unitsLieEquiv A).symm.toLieHom.comp (j.comp N.equiv.symm.toLieHom)
  have hnN : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    N.equiv.nilpotent_iff_equiv_nilpotent.mp hn
  obtain ⟨ρ, hρ, hderiv⟩ := nilpotentSmoothIntegrationInput (E := A) (G := Aˣ) L N
    inferInstance hnN f
  refine ⟨ρ, hρ, ?_⟩
  intro ExpN hExpN x
  have h := hExpN.map_of_mdifferentiable groupExponential_isGroupExponential ρ
    (hρ.mdifferentiable (by simp)) (N.equiv x)
  rw [hderiv, groupExponential_units] at h
  simpa only [f, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    N.equiv.symm_apply_apply, LieEquiv.apply_symm_apply] using h

end PolycyclicRecognition

end

end OAI
