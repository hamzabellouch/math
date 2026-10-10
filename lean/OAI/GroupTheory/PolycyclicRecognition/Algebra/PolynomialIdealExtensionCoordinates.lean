import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCodimensionOneModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectUnipotentRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulRepresentationBCH
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteProductPolynomialCoordinates

namespace OAI

/-! # Extending polynomial exponential coordinates by one dimension

The smaller ideal supplies its polynomial coordinates. The new semidirect
model is represented directly from coordinate translates, so no BCH formula
on the new model is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [LieRing.IsNilpotent L] (C : LieCodimensionOneData L)

theorem polynomialCoordinates_extend_ideal
    (P : letI := C.normedIdeal; PolynomialExponentialCoordinates C.ideal) :
    Nonempty (PolynomialExponentialCoordinates L) := by
  let := C.normedIdeal
  let := P
  let D := C.derivation
  have hD : IsNilpotent D.toLinearMap := C.derivation_nilpotent
  let normedV : NormedAddCommGroup (C.ideal × ℝ) := inferInstance
  let : NormedAddCommGroup (C.ideal × ℝ) := normedV
  let : AddCommGroup (C.ideal × ℝ) := normedV.toAddCommGroup
  let : MetricSpace (C.ideal × ℝ) := normedV.toMetricSpace
  let : UniformSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace
  let : TopologicalSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : ChartedSpace (C.ideal × ℝ) (C.ideal × ℝ) := chartedSpaceSelf _
  let : T0Space (C.ideal × ℝ) := @MetricSpace.instT0Space _ normedV.toMetricSpace
  let : T2Space (C.ideal × ℝ) := inferInstance
  let : CompleteSpace (C.ideal × ℝ) := FiniteDimensional.complete ℝ (C.ideal × ℝ)
  let N := nilpotentModelOfPolynomialIdeal C P
  let _ : Group (C.ideal × ℝ) := derivationSemidirectGroup D hD
  let _ : LieGroup (𝓘(ℝ, C.ideal × ℝ)) ⊤ (C.ideal × ℝ) := derivationSemidirectLieGroup D hD
  have hn := N.tangent_nilpotent (inferInstance : LieRing.IsNilpotent L)
  obtain ⟨m, c, ρ, j, hρ, _, hd, hc⟩ := exists_semidirect_unipotent_representation
    (Module.finBasis ℝ C.ideal) D hD hn
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply polynomialExponentialCoordinates_of_finite_products N
    (inferInstance : LieRing.IsNilpotent L) (universalDynkinCoefficients c)
  intro n X
  exact finite_bch_of_faithful_nilpotent_representation groupExponential
    groupExponential_isGroupExponential ρ hρ j hd c (fun l hl => hc l hl.le) X

end PolycyclicRecognition

end

end OAI
