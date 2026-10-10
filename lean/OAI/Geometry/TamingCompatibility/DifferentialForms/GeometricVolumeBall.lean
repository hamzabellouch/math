import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.GeometricQuadraticMass
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricVolumeGrowth
import OAI.Geometry.TamingCompatibility.Charts.RiemannianChartPowerMass

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms ManifoldVolume ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in
lemma geometricVolume_chart_power_growth (x : X) :
    ∃ p : X, ∃ R C r : ℝ,
      x ∈ (extChartAt Model p).source ∧ 0 < R ∧ 0 ≤ C ∧ 0 < r ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        (geometricVolume A J α).real ((extChartAt Model p).symm '' Metric.closedBall b s) ≤ C*s^4 := by
  have hx := mem_extChartAt_target (I := Model) x
  obtain ⟨δ,hδ,hδt⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := Model) x) _ hx
  let R := δ/8
  have hR : 0 < R := by dsimp [R]; positivity
  have h4 : Metric.closedBall (extChartAt Model x x) (4*R) ⊆ (extChartAt Model x).target := by
    apply Set.Subset.trans _ hδt
    exact Metric.closedBall_subset_ball (by dsimp [R]; linarith)
  obtain ⟨D,hD,hDb⟩ := chart_density_compact_bound J α hs ht x
    (Metric.closedBall (extChartAt Model x x) (4*R)) (isCompact_closedBall _ _) h4
  refine ⟨x,R,D*2^4*volume.real (Metric.closedBall (0:Space) 1),R,mem_extChartAt_source (I := Model) x,
    hR,by positivity,hR,h4,?_⟩
  intro s hs0 b hb
  have hsub : Metric.closedBall b (2*s) ⊆ Metric.closedBall (extChartAt Model x x) (4*R) := by
    intro z hz
    have htri := dist_triangle z b (extChartAt Model x x)
    change dist z (extChartAt Model x x) ≤ 4*R
    change dist z b ≤ 2*s at hz
    change dist b (extChartAt Model x x) ≤ R at hb
    linarith [hs0.2]
  have h := volume_chart_closedBall_bound J α hs ht A x
    (Metric.closedBall (extChartAt Model x x) (4*R)) (isCompact_closedBall _ _) h4
    D hD hDb b hs0.1 hsub
  convert h using 1
  ring

lemma geometricVolume_hermitian_ball_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      (geometricVolume A J α).real {y | hermitianEDist J α hs ht x y < ENNReal.ofReal s} ≤ C*s^4 := by
  let := geometricVolume_finite A J α hs ht
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  exact local_chart_mass_power_to_riemannian (fun x : X => x) (geometricVolume A J α) 4
    (geometricVolume_chart_power_growth J α hs ht A)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
