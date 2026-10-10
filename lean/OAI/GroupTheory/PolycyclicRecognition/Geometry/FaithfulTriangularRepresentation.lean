import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableRepresentationAnnihilator
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SimultaneousAdjointBasis

namespace OAI

/-! # A faithful real triangular representation with nilpotent nilradical

The finite enveloping representation has real split annihilators. Applying
the already proved simultaneous-basis theorem therefore triangularizes it
over the real field, retaining injectivity and nilpotence on the nilradical.
This is the Lie-algebraic part of the Onshuus--Post realization.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [LieAlgebra.IsSolvable L] {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include H in
theorem exists_faithful_triangular_nilradical_representation :
    ∃ m : ℕ, ∃ j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      ∀ x ∈ T.kernelIdeal, IsNilpotent (j x) := by
  let K := CartanNilshadow T H
  let bK := finBasis ℝ K
  let : NormedAddCommGroup K := NormedAddCommGroup.induced K _ bK.equivFun bK.equivFun.injective
  let : NormedSpace ℝ K := NormedSpace.induced ℝ K _ bK.equivFun
  let : RealNormedLieAlgebra K :=
    { (inferInstance : NormedAddCommGroup K), (inferInstance : LieRing K),
      (inferInstance : NormedSpace ℝ K), (inferInstance : LieAlgebra ℝ K) with }
  obtain ⟨c, hfin, hgen⟩ := exists_faithful_truncated_enveloping K (cartanNilshadow_nilpotent T H)
  let := hfin
  let Q := TruncatedEnvelopingAlgebra ℝ K c
  let ρ := solvableTruncatedRepresentation T H c
  let := LieRingModule.compLieHom Q ρ
  let := LieModule.compLieHom Q ρ
  let : LieModule.IsTriangularizable ℝ L Q :=
    ⟨solvableTruncatedRepresentation_genEigenspaces_span T H c⟩
  obtain ⟨m, b, hb⟩ := exists_upperTriangular_lieModule_basis (𝕜 := ℝ) L Q
  let j := (LinearMap.toMatrixAlgEquiv b).toLieEquiv.toLieHom.comp ρ
  refine ⟨m, j, ?_, ?_, ?_⟩
  · exact (LinearMap.toMatrixAlgEquiv b).injective.comp
      (solvableTruncatedRepresentation_injective T H c hgen)
  · exact hb
  · intro x hx
    exact (solvableTruncatedRepresentation_nilpotent T H c x hx).map
      (LinearMap.toMatrixAlgEquiv b).toRingHom

end PolycyclicRecognition

end

end OAI
