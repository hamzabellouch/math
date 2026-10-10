import OAI.Geometry.NodalSets.Charts.MatrixMetricPullback
import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Coefficients.RoundCoefficientJets
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRoundPerturbation

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Matrix Set Metric
open scoped ContDiff RealInnerProductSpace
noncomputable section

def roundSphereEnergyData : SphereEnergyData :=
  ⟨roundCotangentTensor,roundCotangentTensor_smooth,roundCotangentTensor_symm,
    roundCotangentTensor_pos,fun _ ↦ 1,continuous_const,fun _ ↦ zero_lt_one⟩

lemma roundSphereEnergyData_density_smooth :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ roundSphereEnergyData.density := contMDiff_const

lemma roundSphereEnergyData_coefficient :
    intrinsicChartCoefficient roundSphereEnergyData.tensor roundSphereEnergyData.density seedPoint =
      roundCoefficients := by
  funext z
  apply Prod.ext
  · change matrixContravariant (intrinsicSphereChartTensor roundCotangentTensor seedPoint z) =
      ContinuousLinearMap.inverse (roundChartMetric seedPoint z)
    rw [roundCotangentTensor_chart,← matrixCovariant_round]
    symm
    have hA : IsUnit (sphereRoundChartMatrix seedPoint z).det := isUnit_iff_ne_zero.mpr
      (sphereRoundChartMatrix_posDef seedPoint (by rw [centeredSphereChart_target]; trivial)).det_pos.ne'
    apply ContinuousLinearMap.inverse_eq
    · ext alpha v
      have h : baseCovectorCoordinates (matrixCovariant (sphereRoundChartMatrix seedPoint z)
          (matrixContravariant (sphereRoundChartMatrix seedPoint z)⁻¹ alpha)) = baseCovectorCoordinates alpha := by
        rw [matrixCovariant_coordinates,matrixContravariant_coordinates,mulVec_mulVec,
          mul_nonsing_inv _ hA,one_mulVec]
      exact congrArg (fun beta : BaseModel →L[ℝ] ℝ ↦ beta v) (baseCovectorCoordinates_injective h)
    · ext v i
      change (matrixContravariant (sphereRoundChartMatrix seedPoint z)⁻¹
        (matrixCovariant (sphereRoundChartMatrix seedPoint z) v)) i = v i
      have h := matrixContravariant_coordinates (sphereRoundChartMatrix seedPoint z)⁻¹
        (matrixCovariant (sphereRoundChartMatrix seedPoint z) v)
      rw [matrixCovariant_coordinates,mulVec_mulVec,nonsing_inv_mul _ hA,one_mulVec] at h
      exact congrFun h i
  · rfl

lemma roundSphereEnergyData_comparison (r : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient roundSphereEnergyData.tensor roundSphereEnergyData.density seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient roundSphereEnergyData.tensor roundSphereEnergyData.density seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta := by
  intro y _
  simpa only [roundSphereEnergyData_coefficient,roundCoefficientJet,dist_self] using hdelta

lemma roundSphereEnergyData_exterior :
    (∀ x ∉ (∅ : Set Base), ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
      roundSphereEnergyData.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
    (∀ x ∉ (∅ : Set Base), roundSphereEnergyData.density x=1) :=
  ⟨fun x _ v w hv hw ↦ roundCotangentTensor_tangent x v w hv hw,fun _ _ ↦ rfl⟩

end
end Yau.Target

end OAI
