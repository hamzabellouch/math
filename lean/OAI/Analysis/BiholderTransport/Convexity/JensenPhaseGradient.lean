import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.JensenAt
import OAI.Analysis.BiholderTransport.Regularity.ModifiedPhase

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

lemma WeakMTW.jensen_phase_gradient (hmtw:WeakMTW (n:=n) (M:=M))
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
      (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    (coordinatePhaseFlow a (1-t,J.z i,fderiv ℝ
      (chartCenterEnvelope (fun y=>φ (v y)) t a) (J.z i))).2=innerSL ℝ p := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  have H:=hmtw.modified_phase_subgradient
    (s:=Metric.ball (χ (J.Y (J.z i))) r) hu hv hdual hφ.continuous
    ((hφ.differentiable (by simp)).differentiableAt.hasDerivAt (x:=v (J.Y (J.z i))))
    (hslope _).1 (hslope _).2 (sub_pos.mpr ht1) (by linarith : 1-t<1)
    (((J.actual (J.z i) (J.sampleInRegion i)).2.2.1 (J.Y (J.z i))).mpr rfl)
    (J.samples i).1 (χ.map_target hi)
    (by rw [χ.right_inv hi]; exact J.centerDifferentiable _ (J.sampleInRegion i))
    (Metric.mem_ball_self hr) hsem
  simp only [(extChartAt 𝓘(ℝ,Model n) a).right_inv hi] at H
  have HH:=semiconvex_subgradient_eq_at_expansion hA hexp hr K H.2
  apply (InnerProductSpace.toDual ℝ (Model n)).symm.injective
  change _=(InnerProductSpace.toDual ℝ (Model n)).symm ((InnerProductSpace.toDual ℝ (Model n)) p)
  rw [(InnerProductSpace.toDual ℝ (Model n)).symm_apply_apply]
  exact HH

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phase_gradient_tendsto {a:M} {t:ℕ → ℝ} {z:ℕ → Model n}
    {g:ℕ → Model n →L[ℝ] ℝ} {g0:Model n →L[ℝ] ℝ} {p:ℕ → Model n}
    (ht:Tendsto t atTop (𝓝 1))
    (hz:Tendsto z atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hg:Tendsto g atTop (𝓝 g0))
    (hp:∀ᶠ k in atTop,(coordinatePhaseFlow a (1-t k,z k,g k)).2=innerSL ℝ (p k)) :
    Tendsto (fun k=>innerSL ℝ (p k)) atTop (𝓝 g0) := by
  have hτ:Tendsto (fun k=>1-t k) atTop (𝓝 (0:ℝ)):=by
    simpa only [sub_self] using (tendsto_const_nhds.sub ht :
      Tendsto (fun k=>(1:ℝ)-t k) atTop (𝓝 (1-1)))
  have H:=((coordinatePhaseFlow_contDiffAt (q:=(extChartAt 𝓘(ℝ,Model n) a a,g0))
    (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a)).continuousAt.tendsto).comp
    (hτ.prodMk_nhds (hz.prodMk_nhds hg))
  have HH:=H.snd_nhds
  rw [coordinatePhaseFlow_zero (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a)] at HH
  exact HH.congr' hp
end WeakMTWTransport

end

end OAI
