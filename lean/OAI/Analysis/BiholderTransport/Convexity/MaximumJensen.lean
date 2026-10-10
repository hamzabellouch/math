import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumRow
import OAI.Analysis.BiholderTransport.Convexity.JensenAtFirstLimit

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

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma JensenSamplesAt.near_differentiable {v g : M → ℝ} {t : ℝ} {a c : M}
    {N : Set (Model n)} (J : JensenSamplesAt v g t a c N) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) a c),
      DifferentiableAt ℝ (chartOuterEnvelope v t a) z ∧
      DifferentiableAt ℝ (chartCenterEnvelope g t a) z := by
  filter_upwards [J.openRegion.mem_nhds J.centerInRegion] with z hz
  exact ⟨J.outerDifferentiable z hz,J.centerDifferentiable z hz⟩

lemma MaximumRow.jensen_first_limit {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
    Nonempty (ChartFixedPrefixLimit a (modifiedDatum v α D b Bo)
      (hopfLax (1-t) (modifiedDatum v α D b Bc)) t
      (fun k=>e.symm ((extChartAt 𝓘(ℝ,Model n) c).symm (J.z k))) R.q) := by
  have hpole : hopfPole (n := n) t (cTransform (modifiedDatum v α D b Bo)) z=R.q.1.1 := by
    rw [←hmtw.graphHomeomorph_inverse_pole (continuous_modifiedDatum hv α D b ho) ht ht1 z,
      R.graph_inverse hmtw hv ho ht ht1]
  have H := hmtw.jensen_at_first_limit_in_chart (continuous_modifiedDatum hv α D b ho) ht ht1 J hc
    (J.outerGradientContinuous.continuousAt (J.openRegion.mem_nhds J.centerInRegion))
    (J.centerGradientContinuous.continuousAt (J.openRegion.mem_nhds J.centerInRegion))
    J.near_differentiable (hpole ▸ ha)
  dsimp only at H ⊢
  rwa [R.graph_inverse hmtw hv ho ht ht1] at H

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.jensen_center_limit {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    Tendsto (fun k=>extChartAt 𝓘(ℝ,Model n) c (J.Y (J.z k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c (riemannianExp R.q.1.1 R.q.1.2))) := by
  let χ := extChartAt 𝓘(ℝ,Model n) c
  have hdata := J.actual (χ z) J.centerInRegion
  have hval := (hdata.2.2.1 (J.Y (χ z))).mpr rfl
  change hopfLax (1-t) (modifiedDatum v α D b Bc) (χ.symm (χ z))=_ at hval
  rw [χ.left_inv hc] at hval
  have hy : J.Y (χ z)=riemannianExp R.q.1.1 R.q.1.2 := (R.center _).mp hval
  have H := (J.selectorContinuous.continuousAt (J.openRegion.mem_nhds J.centerInRegion)).tendsto.comp J.points
  rwa [hy] at H

end WeakMTWTransport

end

end OAI
