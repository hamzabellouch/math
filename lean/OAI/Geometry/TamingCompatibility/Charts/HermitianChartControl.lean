import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricDistance

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms Set Filter GeometricHilbert.GeometricNormalCharts
open scoped Manifold ContDiff Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
lemma compact_hermitian_chart_control (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x y : X,
      x ∈ (extChartAt Model p).source → y ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → extChartAt Model p y ∈ K →
      ‖extChartAt Model p x-extChartAt Model p y‖ ≤ L*(hermitianEDist J α hs ht x y).toReal := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let := geometricMetricSpace J α hs ht
  obtain ⟨L,hL,hbound⟩ := compact_chart_distance_control p hK hKT
  refine ⟨max 1 (L:ℝ),le_max_left _ _,fun x y hxs hys hxK hyK => ?_⟩
  have hh := hbound x y hxs hys hxK hyK
  change edist (extChartAt Model p x) (extChartAt Model p y) ≤ (L:ℝ≥0∞)*hermitianEDist J α hs ht x y at hh
  have ht' : (L:ℝ≥0∞)*hermitianEDist J α hs ht x y ≠ ⊤ := by
    change (L:ℝ≥0∞)*edist x y ≠ ⊤
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top x y)
  have hh' := ENNReal.toReal_mono ht' hh
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,← dist_edist,dist_eq_norm] at hh'
  exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)
end TamingCompatibility

end
end

end OAI
