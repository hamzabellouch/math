import OAI.Probability.SLE.Geometry.SimpleSlitConnected
import TauCeti.Analysis.Complex.Conformal.SimplyConnected

namespace OAI

/-! Conformal charts for arbitrary finite simple attached arcs, using
the Riemann mapping theorem and connectedness of the complement. -/
noncomputable section
open Set Complex Metric Function

namespace SLEExactGauge

theorem simple_arc_halfPlane_simplyConnected
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    IsSimplyConnected (upperHalfPlane \ range p) := by
  have ho : IsOpen (upperHalfPlane \ range p) :=
    isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed
  apply TauCeti.isSimplyConnected_of_filledHull_subset ho
    (simple_arc_halfPlane_complement_connected p hi h0 hH)
  exact (TauCeti.filledHull_eq_self (attached_arc_domain_complement_preconnected p h0)
    (attached_arc_domain_complement_unbounded p)).le

theorem simple_arc_exists_disk_chart
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ f : ℂ → ℂ, BijOn f (upperHalfPlane \ range p) (ball 0 1) ∧
      DifferentiableOn ℂ f (upperHalfPlane \ range p) ∧
      DifferentiableOn ℂ (invFunOn f (upperHalfPlane \ range p)) (ball 0 1) ∧
      LeftInvOn (invFunOn f (upperHalfPlane \ range p)) f (upperHalfPlane \ range p) ∧
      RightInvOn (invFunOn f (upperHalfPlane \ range p)) f (ball 0 1) := by
  have ho : IsOpen (upperHalfPlane \ range p) :=
    isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed
  apply TauCeti.exists_bijOn_ball_differentiableOn_invFunOn ho
    (simple_arc_halfPlane_simplyConnected p hi h0 hH)
  intro he
  have hz : (0:ℂ) ∈ upperHalfPlane \ range p := by rw [he]; trivial
  exact (lt_irrefl (0:ℝ)) hz.1

end SLEExactGauge

end

end OAI
