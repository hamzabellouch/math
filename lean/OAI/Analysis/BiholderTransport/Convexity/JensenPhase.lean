import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.JensenAt
import OAI.Analysis.BiholderTransport.Regularity.ModifiedPhase
import OAI.Analysis.BiholderTransport.Calculus.PhaseGraphDerivative

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_phase_graph_identity (hmtw:WeakMTW (n:=n) (M:=M))
    {u v w:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℝ → ℝ} (hφ:ContDiff ℝ ∞ φ)
    (hslope:∀y:M,0<deriv φ (v y) ∧ deriv φ (v y)<1)
    {a c:M} {N:Set (Model n)} {t:ℝ} (ht:0<t) (ht1:t<1)
    (J:JensenSamplesAt w (fun y=>φ (v y)) t a c N) (i:ℕ)
    (hi:J.z i∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {p:Model n} {A:Model n →L[ℝ] Model n} {r K:ℝ} (hr:0<r)
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hexp:HasQuadraticExpansion (fun h=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm
      (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z i))+h)))) p A)
    (hsem:ConvexOn ℝ (Metric.ball (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z i))) r)
      (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2))
    (hflow:DifferentiableAt ℝ (fun q:Phase n=>coordinatePhaseFlow a (1-t,q))
      (J.z i,fderiv ℝ (chartCenterEnvelope (fun y=>φ (v y)) t a) (J.z i))) :
    (fderiv ℝ (fun q:Phase n=>coordinatePhaseFlow a (1-t,q))
      (J.z i,fderiv ℝ (chartCenterEnvelope (fun y=>φ (v y)) t a) (J.z i))).comp
      ((ContinuousLinearMap.id ℝ (Model n)).prod
        (fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ (v y)) t a)) (J.z i)))=
      (fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a (J.Y z)) (J.z i)).prod
        (((innerSL ℝ).comp A).comp
          (fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a (J.Y z)) (J.z i))) := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let G:=chartCenterEnvelope (n := n) (fun y=>φ (v y)) t a
  have hY:HasFDerivAt (fun z=>χ (J.Y z)) (fderiv ℝ (fun z=>χ (J.Y z)) (J.z i)) (J.z i) :=
    (J.samples i).2.2.2.2.1
  have hsub:∀ᶠ z in 𝓝 (J.z i),
      (coordinatePhaseFlow a (1-t,z,fderiv ℝ G z)).1=χ (J.Y z) ∧
      IsSemiconvexSubgradientOn (fun q=>φ (v (χ.symm q))) (Metric.ball (χ (J.Y (J.z i))) r) K
        (χ (J.Y z)) ((InnerProductSpace.toDual ℝ (Model n)).symm
          (coordinatePhaseFlow a (1-t,z,fderiv ℝ G z)).2) := by
    filter_upwards [J.openRegion.mem_nhds (J.sampleInRegion i),
      (isOpen_extChartAt_target a).mem_nhds hi,
      hY.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)] with z hz hzt hball
    have H:=hmtw.modified_phase_subgradient (s := Metric.ball (χ (J.Y (J.z i))) r) hu hv hdual hφ.continuous
      ((hφ.differentiable (by simp)).differentiableAt.hasDerivAt (x := v (J.Y z)))
      (hslope _).1 (hslope _).2 (sub_pos.mpr ht1) (by linarith : 1-t<1)
      (((J.actual z hz).2.2.1 (J.Y z)).mpr rfl) (J.actual z hz).1 (χ.map_target hzt)
      (by rw [χ.right_inv hzt]; exact J.centerDifferentiable z hz) hball hsem
    simpa only [χ, G, chartCenterEnvelope, (extChartAt 𝓘(ℝ,Model n) a).right_inv hzt] using H
  exact semiconvex_phase_graph_derivative hA hexp hr K hY
    ((J.samples i).2.2.2.2.2.2.2.2.1.hasFDerivAt) hflow.hasFDerivAt
    (hsub.mono (fun _ h=>h.1)) (hsub.mono (fun _ h=>h.2))

end WeakMTWTransport

end

end OAI
