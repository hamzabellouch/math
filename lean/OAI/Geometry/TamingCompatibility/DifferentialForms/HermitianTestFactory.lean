import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianOff

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set Filter
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma exists_radial_test_data (p : A.centers) {z : Space} (hz : z ∈ (D p).domain)
    (hwz : coordinateWeight A p z ≠ 0) :
    ∃ τ ρ φ : 𝓢(Space,ℝ), ∃ U : Set Space, ∃ R : ℝ,
      IsOpen U ∧ z ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ y ∈ U, τ y * coordinateWeight A p y = 1) ∧
      (∀ y ∈ U, ρ y = chartDensity J α p.val y) ∧
      HasCompactSupport (φ : Space → ℝ) ∧ tsupport φ ⊆ (D p).domain ∧
      0 < R ∧ 2*R ≤ 1 ∧ Metric.closedBall z (4*R) ⊆ U ∧
      (∀ y ∈ Metric.closedBall z (4*R), φ y = 1) ∧
      ∀ b ∈ Metric.closedBall z R, Metric.closedBall b (2*R) ⊆ Metric.closedBall z (4*R) := by
  obtain ⟨τ,ρ,U,hU,hzU,hUD,hτ,hρ⟩ := exists_coordinate_observer A J α hs ht D p hz hwz
  obtain ⟨φ,hφ,hφU,V,hV,hzV,hVU,hφone⟩ := SchwartzCutoff.exists_one_near hU hzU
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV z hzV
  let R := min (r/8) (1/2:ℝ)
  have hR : 0 < R := lt_min (by positivity) (by norm_num)
  have hRr : R ≤ r/8 := min_le_left _ _
  have hR1 : R ≤ 1/2 := min_le_right _ _
  have hballV : Metric.closedBall z (4*R) ⊆ V := by
    intro y hy
    apply hrV
    rw [Metric.mem_ball]
    have hd : dist y z ≤ 4*R := Metric.mem_closedBall.mp hy
    linarith
  refine ⟨τ,ρ,φ,U,R,hU,hzU,hUD,hτ,hρ,hφ,hφU.trans hUD,hR,by linarith,
    hballV.trans hVU,fun y hy => hφone y (hballV hy),?_⟩
  intro b hb y hy
  rw [Metric.mem_closedBall] at hb hy ⊢
  have ht := dist_triangle y b z
  linarith
end TamingCompatibility.GeometricHilbert

end

end OAI
