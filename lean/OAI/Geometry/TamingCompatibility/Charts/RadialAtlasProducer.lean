import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianTestFactory
import OAI.Geometry.TamingCompatibility.Concentration.RadialDefectFinite

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open GeometricHilbert GeometricHilbert.Hermitian Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

theorem separating_probability_atlas_defect
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (A : FiniteCharts X) (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) (x : X) (hp : A.partition p x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt Model p.val x) r ⊆ (extChartAt Model p.val).target ∧
      Integrable (smoothUnitDefect J α hs ht p.val (extChartAt Model p.val x) r 0) μ := by
  obtain ⟨G,H,Gs,hH,_hHclosed,_hGs,hweak,B,hB,hdual⟩ :=
    exists_smooth_inverse_dual_data A J α hs ht D hA
  have hx := hA p (subset_closure hp)
  have hz : extChartAt Model p.val x ∈ (D p).domain :=
    (D p).small_ball_subset (Metric.ball_subset_closedBall hx.2)
  have hxsrc := (D p).source_subset (hA p (subset_closure hp))
  have hwz : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxsrc] using hp
  obtain ⟨τ,ρ,φ,U,R,hU,_hzU,hUD,hτ,hρ,hφc,hφD,hR,hR1,hballU,hφone,hcenters⟩ :=
    exists_radial_test_data A J α hs ht D p hz hwz
  obtain ⟨C,r,hC,hr,hrR,hbound⟩ := separating_probability_smooth_defect
    J α hs ht A D hA H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    (φ.smooth ⊤) hφc hφD (Metric.closedBall (extChartAt Model p.val x) (4*R))
    (isCompact_closedBall _ _) hballU hφone R hR
    (Metric.closedBall (extChartAt Model p.val x) R) (isCompact_closedBall _ _) hcenters hR1 μ hann
  have hb : extChartAt Model p.val x ∈ Metric.closedBall (extChartAt Model p.val x) R :=
    Metric.mem_closedBall_self hR.le
  have htarget : Metric.closedBall (extChartAt Model p.val x) r ⊆ (extChartAt Model p.val).target :=
    (Metric.closedBall_subset_closedBall (hrR.trans (by linarith))).trans
      ((hcenters _ hb).trans (hballU.trans (hUD.trans (D p).domain_subset)))
  exact ⟨r,hr,htarget,(singularDefect_integrable_of_bounds J α hs ht p.val
    (extChartAt Model p.val x) hr hC htarget μ (fun s hs => hbound s hs _ hb)).1⟩
end TamingCompatibility

end
end

end OAI
