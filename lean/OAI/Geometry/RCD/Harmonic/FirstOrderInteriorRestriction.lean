import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Restriction of the original splitting maps to moving interior centers -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.first_order_interior_restriction {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {c : ℝ} (hc : 0<c) (hc1 : c≤1) :
    ∃ D : ℝ, 1≤D ∧ ∀ (p q : X) (r ε : ℝ), 0<r → -1≤K*(80*r)^2 →
      dist q p≤r → 0≤ε →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (80*r) ε u v →
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (16*(c*r)) (D*ε) u v := by
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn
    (a:=1) (δ:=c/5) (by norm_num) (by positivity) (by linarith)
  refine ⟨D,hD,?_⟩
  intro p q r ε hr hcurv hqp hε u v hs
  have hsub : ball q (16*(c*r))⊆ball p (80*r) := by
    intro x hx
    change dist x p<80*r
    have hh := dist_triangle x q p
    have hcr : c*r≤r := mul_le_of_le_one_left hr.le hc1
    change dist x q<16*(c*r) at hx
    linarith
  have hvolume := hvol p (80*r) (by positivity) hcurv q (by linarith)
  have he : c/5*(80*r)=16*(c*r) := by ring
  rw [he] at hvolume
  exact hs.restrict_ball (hausdorff n X) hX.quadratic hsub hε hD
    (hX.fullSupport _ _ (by positivity)).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
    (hX.fullSupport _ _ (by positivity)).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne hvolume

end RegularPointCoordinates

end

end OAI
