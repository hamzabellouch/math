import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma metric_local_growth_of_normal {f : M → ℝ} {x : M} {b : ℝ}
    (h : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      b*‖v‖^2≤f (riemannianExp x v)-f x) :
    ∀ᶠ z in 𝓝 x, b*dist x z^2≤f z-f x := by
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp h
  filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
  obtain ⟨v,hv,he⟩ := exists_minimizing_vector (n := n) x z
  have hd : ‖v‖=dist x z := by simpa only [minimizingVectors,mem_ofPred_eq,he] using hv.symm
  have hh := hball (y := v) (by simpa only [Metric.mem_ball,dist_zero_right,hd,dist_comm] using hz)
  simpa only [he,hd] using hh

lemma WeakMTW.active_hull_metric_growth (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x), t • q ∈ injectivityDomain x) :
    ∃ b>0, ∀ᶠ z in 𝓝 x,
      b*dist x z^2 ≤ cTransform v z-cTransform v x+
        (cost z (riemannianExp x (t • p))-cost x (riemannianExp x (t • p)))/t := by
  obtain ⟨b,hb,H⟩ := hmtw.active_hull_local_growth hv hp ht ht1 hID
  refine ⟨b,hb,?_⟩
  have hh := metric_local_growth_of_normal (n := n)
    (f := fun z => cTransform v z+cost z (riemannianExp x (t • p))/t)
    (b := b) (x := x) (by
      filter_upwards [H] with h hh
      rw [sub_div] at hh
      linarith)
  filter_upwards [hh] with z hz
  rw [sub_div]
  linarith

lemma WeakMTW.active_hull_strict_local_min (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x), t • q ∈ injectivityDomain x) :
    ∀ᶠ z in 𝓝 x, z≠x →
      cTransform v x+cost x (riemannianExp x (t • p))/t <
        cTransform v z+cost z (riemannianExp x (t • p))/t := by
  obtain ⟨b,hb,H⟩ := hmtw.active_hull_metric_growth hv hp ht ht1 hID
  filter_upwards [H] with z hz hzx
  have hd : 0<dist x z := dist_pos.mpr hzx.symm
  have hpos := mul_pos hb (sq_pos_of_pos hd)
  rw [sub_div] at hz
  linarith

end WeakMTWTransport

end

end OAI
