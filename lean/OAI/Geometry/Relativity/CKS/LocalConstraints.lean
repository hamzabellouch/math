import OAI.Geometry.Relativity.CKS.ConstraintDensityDefinitions

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSIntrinsicConstraints
lemma coordinateMomentumNorm_continuousAt {A B : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hsym : ∀ v w, A x v w = A x w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    ContinuousAt (coordinateMomentumNorm A B) x := by
  have hg := physicalMetricJet_continuousAt (spatialCoefficients_smooth hA)
    (spatialCoefficients_positive hsym hpos).det_pos.ne'
  have hk := physicalTensorJet_continuousAt (spatialCoefficients_smooth hB)
  exact (hg.momentumSq hk).sqrt.comp CKSCartesianOuter.toPoint.continuous.continuousAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}
def ConstraintChart.at (c : ConstraintChart g K x) (y : M) (hy : y ∈ c.domain) :
    ConstraintChart g K y := { c with mem := hy }
omit [IsManifold I ∞ M] in
lemma ConstraintChart.continuous_energy [IsManifold I ∞ M] (c : ConstraintChart g K x) :
    ContinuousOn (fun y => spatialEnergy c.metric c.tensor (c.coordinate y)) c.domain := by
  intro y hy
  exact (spatial_energy_continuousAt (c.coefficientSmooth y hy).1
    (c.coefficientSmooth y hy).2 (c.positiveSymmetric y hy).1
    (c.positiveSymmetric y hy).2.1).comp_continuousWithinAt
      (c.smooth.continuousOn y hy)
omit [IsManifold I ∞ M] in
lemma ConstraintChart.continuous_momentumNorm [IsManifold I ∞ M] (c : ConstraintChart g K x) :
    ContinuousOn (fun y => coordinateMomentumNorm c.metric c.tensor (c.coordinate y)) c.domain := by
  intro y hy
  exact (coordinateMomentumNorm_continuousAt (c.coefficientSmooth y hy).1
    (c.coefficientSmooth y hy).2 (c.positiveSymmetric y hy).1
    (c.positiveSymmetric y hy).2.1).comp_continuousWithinAt
      (c.smooth.continuousOn y hy)
end CKSIntrinsicConstraints

end

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CKSAngularGeometry
lemma momentumSq_eq_frame {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x) (hk : ContDiffAt ℝ ∞ K x) :
    CKSLocalBending.momentumSq (physicalMetricJet G x) (physicalTensorJet K x) =
      ∑ a, (actualFrameMomentum G K E x a)^2 := by
  rw [physical_momentum_frame_norm_general h (hk.differentiableAt (by simp))]
  simp only [metricPair,physicalMetricJet_momentum h.metric_smooth hk h.positive.det_pos.ne' h.symmetric]
  rfl

lemma local_coordinate_momentumSq_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G E y)
    (hK : ContDiffAt ℝ ∞ K (e x)) :
    CKSLocalBending.momentumSq (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) =
    CKSLocalBending.momentumSq (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) := by
  have h : ∀ᶠ y in 𝓝 x, FrameChartAt e G (coordinatePullback e G) E
      (coordinatePullbackFrame e E) y := by
    filter_upwards [e.open_source.mem_nhds hx,he,
      he.self_of_nhds.continuousAt.eventually hi,he.self_of_nhds.continuousAt.eventually hE]
      with y hy hey hiy hEy
    exact smooth_coordinate_pullback_frame_at e G E hy hey hiy hEy
  have hc := h.self_of_nhds
  have hk' := coordinatePullback_smooth hc.chart_smooth hK
  have hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (coordinatePullback e K y) v w =
      metricPair (K (e y)) (fderiv ℝ e y v) (fderiv ℝ e y w) :=
    Eventually.of_forall fun y => coordinatePullback_pair e K y
  obtain ⟨_,_,hJ⟩ := actual_constraints_chart_covariance h hK hkl
  rw [momentumSq_eq_frame hc.target hk',momentumSq_eq_frame hc.source hK]
  simp_rw [hJ]
end CKSAngularGeometry

end

end OAI
