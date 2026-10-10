import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ChartFirstMatrix
import OAI.Analysis.BiholderTransport.Convexity.JensenAt

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_at_first_limit_in_chart (hmtw : WeakMTW (n := n) (M := M))
    {v g : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {a c d : M} {N : Set (Model n)} (J : JensenSamplesAt v g t d c N)
    (hcd : c∈(extChartAt 𝓘(ℝ,Model n) d).source)
    (hF : ContinuousAt (fderiv ℝ (chartOuterEnvelope v t d)) (extChartAt 𝓘(ℝ,Model n) d c))
    (hC : ContinuousAt (fderiv ℝ (chartCenterEnvelope g t d)) (extChartAt 𝓘(ℝ,Model n) d c))
    (hnear : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) d c),
      DifferentiableAt ℝ (chartOuterEnvelope v t d) z ∧
      DifferentiableAt ℝ (chartCenterEnvelope g t d) z)
    (ha : hopfPole (n := n) t (cTransform v) c∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) d
    let e := hmtw.graphHomeomorph hv ht ht1
    Nonempty (ChartFixedPrefixLimit a v (hopfLax (1-t) g) t
      (fun k=>e.symm (χ.symm (J.z k))) (e.symm c)) := by
  let χ := extChartAt 𝓘(ℝ,Model n) d
  let e := hmtw.graphHomeomorph hv ht ht1
  let q := fun k=>e.symm (χ.symm (J.z k))
  let q₀ := e.symm c
  have hproj : ∀ k,graphProjection (cTransform v) t (q k)=χ.symm (J.z k) :=
    fun k=>e.apply_symm_apply _
  have hproj₀ : graphProjection (cTransform v) t q₀=c := e.apply_symm_apply c
  have hat := χ.map_source hcd
  have hleft : χ.symm (χ c)=c := χ.left_inv hcd
  have hzman : Tendsto (fun k=>χ.symm (J.z k)) atTop (𝓝 c) := by
    have hc : ContinuousAt χ.symm (χ c) := continuousAt_extChartAt_symm'' hat
    have H := hc.tendsto.comp J.points
    rwa [hleft] at H
  have hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)) := by
    simpa only [hproj,hproj₀] using hzman
  have he : ∀ᶠ k in atTop,χ (graphProjection (cTransform v) t (q k))=J.z k := by
    filter_upwards [J.points.eventually ((isOpen_extChartAt_target d).mem_nhds hat)] with k hk
    rw [hproj]
    exact χ.right_inv hk
  have hc : graphProjection (cTransform v) t q₀∈χ.source :=
    hproj₀ ▸ hcd
  have hpole : q₀.1.1=chartActualPole v t d (χ c) := by
    dsimp only [chartActualPole]
    rw [hleft]
    exact hmtw.graphHomeomorph_inverse_pole hv ht ht1 c
  have hder : ∀ᶠ k in atTop,
      DifferentiableAt ℝ (fderiv ℝ (chartOuterEnvelope v t d))
        (χ (graphProjection (cTransform v) t (q k))) ∧
      DifferentiableAt ℝ (fderiv ℝ (chartCenterEnvelope g t d))
        (χ (graphProjection (cTransform v) t (q k))) ∧
      DifferentiableAt ℝ (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) q₀.1.1
        (chartActualPole v t d w)) (χ (graphProjection (cTransform v) t (q k))) := by
    filter_upwards [he] with k hk
    rw [hk,hpole]
    have H := J.samples k
    exact ⟨H.2.2.2.2.2.2.2.1,H.2.2.2.2.2.2.2.2.1,H.2.2.2.2.2.1.differentiableAt⟩
  have ha0 : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source := by
    rw [hmtw.graphHomeomorph_inverse_pole hv ht ht1 c]
    exact ha
  apply hmtw.first_fixed_prefix_limit_in_chart hv ht ht1 q q₀ hz ha0 hc
    (mem_extChartAt_source q₀.1.1) J.Af J.Ac
  · simpa only [hproj₀] using hF
  · simpa only [hproj₀] using hC
  · simpa only [hproj₀] using hnear
  · exact J.outerHessians.congr' (he.mono (fun k hk=>congrArg
      (fderiv ℝ (fderiv ℝ (chartOuterEnvelope v t d))) hk.symm))
  · exact J.centerHessians.congr' (he.mono (fun k hk=>congrArg
      (fderiv ℝ (fderiv ℝ (chartCenterEnvelope g t d))) hk.symm))
  · exact J.gradients.congr' (he.mono (fun k hk=>congrArg
      (fun z=>fderiv ℝ (chartOuterEnvelope v t d) z+fderiv ℝ (chartCenterEnvelope g t d) z) hk.symm))
  · exact J.upper
  · exact hder

end WeakMTWTransport

end

end OAI
