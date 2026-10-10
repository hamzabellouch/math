import OAI.Geometry.SurfaceImmersion.Whitney.ActualRuledRectangle
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapArcGermRestriction

namespace OAI

/-! The supported replacement retains actual endpoint crosscap charts
 and the same full source strip, rather than just formal derivative data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}
variable {S : CrosscapCoordinateStrip A} {c d : ℝ}

theorem ActualRuledRectangle.crosscap_strip (R : ActualRuledRectangle S c d) :
    ∃ (B : CrosscapConnectingArc R.replacement p q) (T : CrosscapCoordinateStrip B),
      B.arc = A.arc ∧ T.chart = S.chart ∧ T.model = R.model ∧ T.domain = S.domain := by
  obtain ⟨B,hB⟩ := A.restrict_germs R.left_germ R.right_germ R.regular_iff
  have hfirst : ∀ t, fderiv ℝ R.model (![0,t] : Base) =
      fderiv ℝ S.model (![0,t] : Base) := by
    intro t
    simpa only [crosscapAxis_apply] using (R.axis_jets t).2.1
  let T : CrosscapCoordinateStrip B := {
    chart := S.chart
    width := S.width
    width_pos := S.width_pos
    chart_smooth := S.chart_smooth
    inverse_smooth := S.inverse_smooth
    model := R.model
    model_smooth := R.model_smooth
    domain := S.domain
    domain_open := S.domain_open
    domain_target := S.domain_target
    model_eq := R.model_eq
    axis := by simpa only [hB] using S.axis
    rectangle := by simpa only [hB] using S.rectangle
    transverse := by
      intro t ht
      rw [hfirst]
      exact S.transverse t (by simpa only [hB] using ht)
    interior_regular := by
      intro t ht
      rw [hfirst]
      exact S.interior_regular t (by simpa only [hB] using ht)
    left_vertical := by
      rw [hB,hfirst]
      exact S.left_vertical
    right_vertical := by
      rw [hB,hfirst]
      exact S.right_vertical }
  exact ⟨B,T,hB,rfl,rfl,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
