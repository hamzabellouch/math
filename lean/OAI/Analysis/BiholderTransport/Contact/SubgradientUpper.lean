import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalSubdifferential
import OAI.Analysis.BiholderTransport.Contact.MovingCostSupport
import OAI.Analysis.BiholderTransport.Convexity.CompactConvexHullFinite

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma normalSubdifferential_directional_le {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈normalSubdifferential u x)
    (h : TangentSpace 𝓘(ℝ,Model n) x) {K : ℝ}
    (hK : ∀ᶠ t : ℝ in 𝓝 0, 0≤t → u (riemannianExp x (t • h))-u x≤K*t) :
    inner ℝ p h≤K := by
  by_contra hn
  have hdiff : 0 < inner ℝ p h-K := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (inner ℝ p h-K)/(2*(‖h‖+1))
  have hn1 : 0<‖h‖+1 := by positivity
  have hε : 0<ε := div_pos hdiff (mul_pos (by norm_num) hn1)
  have he : ε*(2*(‖h‖+1))=inner ℝ p h-K := div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hn1))
  have hc : Tendsto (fun t : ℝ => t • h) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t • h) 0 := continuousAt_id.smul continuousAt_const
    simpa only [zero_smul] using hc.tendsto
  have H := (hc.eventually (hp ε hε)).and hK
  obtain ⟨δ,hδ,Hδ⟩ := Metric.eventually_nhds_iff.mp H
  have ht : 0<δ/2 := by positivity
  have hh := Hδ (y := δ/2) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using (show δ/2<δ by linarith))
  have hb := hh.1.trans (hh.2 ht.le)
  rw [inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hb
  have hb' : (inner ℝ p h-ε*‖h‖)*(δ/2)≤K*(δ/2) := by nlinarith [hb]
  have Hbad := (mul_le_mul_iff_left₀ ht).mp hb'
  nlinarith [mul_pos hε hn1]

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalSubdifferential_subset_active_hull {v : M → ℝ} (hv : Continuous v) (x : M) :
    normalSubdifferential (cTransform v) x ⊆ convexHull ℝ (activeLogs (n := n) v x) := by
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  have : CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x) := FiniteDimensional.complete ℝ _
  intro p hp
  by_contra hn
  obtain ⟨f,K,hK,hpK⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (activeLogs (n := n) v x))
    (isCompact_convexHull_finiteDimensional (isCompact_activeLogs (n := n) hv x)).isClosed hn
  let h := (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).symm f
  have he : ∀ q : TangentSpace 𝓘(ℝ,Model n) x, inner ℝ q h=f q := by
    intro q
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hh := active_directional_upper_support hv h
    (fun q hq => by rw [he]; exact hK q (subset_convexHull ℝ _ hq))
  have H := normalSubdifferential_directional_le hp h hh
  rw [he] at H
  exact (not_lt_of_ge H hpK)
end WeakMTWTransport

end

end OAI
