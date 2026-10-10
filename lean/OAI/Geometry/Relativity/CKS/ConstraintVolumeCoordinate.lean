import OAI.Geometry.Relativity.CKS.VolumeCoordinate

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSIntrinsicConstraints
lemma spatialCartesian_eq_gram (A : SpatialTensor) (x : E) :
    spatialCartesian A x = LinearMap.BilinForm.toMatrix CKSIntrinsicVolume.stdBasis (A x).toBilinForm := by
  ext i j
  simp only [spatialCartesian,spatialCoefficients,ContinuousLinearEquiv.symm_apply_apply,
    LinearMap.BilinForm.toMatrix_apply,CKSIntrinsicVolume.stdBasis,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.toBilinForm_apply]
  congr 2
lemma spatialVolume_eq_density (A : SpatialTensor) :
    spatialVolume A = volume.withDensity (fun y => ENNReal.ofReal (CKSIntrinsicVolume.coordinateDensity A y)) := by
  simp only [spatialVolume,spatialCartesian_eq_gram,CKSIntrinsicVolume.coordinateDensity]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
lemma riemannianVolume_end (g : SmoothMetric I (M := M))
    (e : OpenPartialHomeomorph M E) (A : SpatialTensor)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ e e.source)
    (hrep : ∀ x ∈ e.source, g.inner x = endInner I e A x) :
    (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric).restrict e.source =
      Measure.map e.symm ((spatialVolume A).restrict e.target) := by
  rw [CKSIntrinsicVolume.riemannianVolume_coordinate g.toContinuousRiemannianMetric e A
    (hf.of_le (by simp)) (fun x hx v w => congrArg (fun a => a v w) (hrep x hx)),
    CKSIntrinsicVolume.coordinateMeasure,spatialVolume_eq_density]
  rw [restrict_withDensity e.open_target.measurableSet]

end CKSIntrinsicConstraints

end

end OAI
