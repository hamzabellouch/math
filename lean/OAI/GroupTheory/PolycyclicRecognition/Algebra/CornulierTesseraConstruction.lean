import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationTriangulableModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactExtensionModels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SolvableGroupLieAlgebra

namespace OAI

/-! # Constructing the Cornulier–Tessera comparison

The original group and its real rotational modification both embed properly
and cocompactly in the same compact semidirect extension. The modification's
analytic chart and closed triangular realization have been constructed above.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

theorem cornulierTesseraModelInput : CornulierTesseraModelInput := by
  intro S
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let metric : MetricSpace S.carrier := d.compatibleMetric
  let L := GroupLieAlgebra (𝓘(ℝ,S.modelSpace)) S.carrier
  let solv : LieAlgebra.IsSolvable L :=
    groupLieAlgebra_isSolvable (E := S.modelSpace) (G := S.carrier)
  obtain ⟨n,b,hb⟩ := exists_complex_triangular_adjoint_basis L
  let T : ComplexTriangularAdjoint L n := ⟨b,hb⟩
  obtain ⟨x,hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℝ L
  let H := LieSubalgebra.engel ℝ x
  let cartan : H.IsCartanSubalgebra := hx
  let Exp := groupExponential (E := S.modelSpace) (G := S.carrier)
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  obtain ⟨F⟩ := nonempty_complexWeightFactorModel T H Exp hExp
  obtain ⟨R,hR,hf⟩ := F.exists_triangulable_rotation_model hExp
  let S₁ := S.toLCModel
  let S₂ := compactSemidirectLCModel S₁ (realRotationTorus L H)
    (F.factorCompactRotationAction hExp) (F.continuous_factorCompactRotationAction hExp)
  exact ⟨R,hR,S₁,S₂,⟨ProperCocompactHom.id S.carrier⟩,
    ⟨F.originalToSmoothRotationExtension hExp⟩,hf⟩

end PolycyclicRecognition

end

end OAI
