import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.PoleCoordinates

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def WeakMTW.graphHomeomorph (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    subgradientGraph (n := n) (cTransform v) ≃ₜ M :=
  (Equiv.ofBijective (graphProjection (cTransform v) t)
    ⟨hmtw.injective_graphProjection hv ht ht1,
      surjective_graphProjection (continuous_cTransform hv) ht⟩).toHomeomorphOfContinuousOpen
    (continuous_graphProjection _ _) (hmtw.isOpenMap_graphProjection hv ht ht1
      (fun x p hp=>hmtw.active_hull_precut hv ht ht1 x p
        (normalSubdifferential_subset_active_hull hv x hp)))

lemma WeakMTW.graphHomeomorph_inverse_pole (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    ((hmtw.graphHomeomorph hv ht ht1).symm z).1.1=hopfPole (n := n) t (cTransform v) z := by
  let q := (hmtw.graphHomeomorph hv ht ht1).symm z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  change hopfPole (n := n) t (cTransform v)
    ((hmtw.graphHomeomorph hv ht ht1) q)=q.1.1 at H
  simpa only [q,Homeomorph.apply_symm_apply] using H.symm

lemma WeakMTW.graph_points_tendsto (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {q : ℕ → subgradientGraph (n := n) (cTransform v)}
    {q₀ : subgradientGraph (n := n) (cTransform v)}
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀))) :
    Tendsto (fun k=>(q k).1) atTop (𝓝 q₀.1) := by
  have H := (hmtw.graphHomeomorph hv ht ht1).symm.continuous.tendsto
    ((hmtw.graphHomeomorph hv ht ht1) q₀)
  have H' := H.comp hz
  change Tendsto (fun k=>(hmtw.graphHomeomorph hv ht ht1).symm
    ((hmtw.graphHomeomorph hv ht ht1) (q k))) atTop
    (𝓝 ((hmtw.graphHomeomorph hv ht ht1).symm
      ((hmtw.graphHomeomorph hv ht ht1) q₀))) at H'
  simp only [Homeomorph.symm_apply_apply] at H'
  exact continuous_subtype_val.tendsto q₀ |>.comp H'

end WeakMTWTransport

end

end OAI
