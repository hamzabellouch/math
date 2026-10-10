import OAI.Geometry.IsometricImmersion.Taylor.ActualTaylorFiniteJets

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation
open SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem upper_cauchy_jets_of_actual_coordinate_bound
    {P : Coord → ℝ} {radius a delta tau C : ℝ} {N : ℕ}
    (hP : ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-radius) radius)))
    (ha : a < radius) (ht : 0 ≤ delta/tau)
    (hB : CoordinateBound P (pulseStrip a delta tau) (N+1) C)
    {x : ℝ} (hx : |x| ≤ a) :
    ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (heightCauchyValue P (delta/tau)) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity P (delta/tau)) x‖ ≤ C := by
  have hp : coordinatePoint x (delta/tau) ∈ pulseStrip a delta tau := by
    have hp0 : x ∈ Icc (-a) a ∧ delta/tau ∈ Icc (-(delta/tau)) (delta/tau) :=
      ⟨abs_le.mp hx,⟨(neg_nonpos.mpr ht).trans ht,le_rfl⟩⟩
    simpa [coordinatePoint,pulseStrip,SmoothLocal.Weighted.closedRectangle] using hp0
  have hpU : coordinatePoint x (delta/tau) ∈ spatialStrip (Ioo (-radius) radius) := by
    have hxU : x ∈ Ioo (-radius) radius :=
      ⟨(neg_lt_neg ha).trans_le (abs_le.mp hx).1,(abs_le.mp hx).2.trans_lt ha⟩
    simpa [coordinatePoint,spatialStrip] using hxU
  have hval : |P (coordinatePoint x (delta/tau))| ≤ C := hB [] (by simp) _ hp
  have hjet : ∀ i : Fin 2, ∀ n ≤ N,
      |spatialJet (spatialFirstJet P i) n (coordinatePoint x (delta/tau))| ≤ C := by
    intro i n hn
    exact coordinateBound_spatialFirstJet hB hn i hp
  simpa only [max_self] using cauchy_fullJets_of_actual_spatial_firstJets
    hP (spatialStrip_isOpen isOpen_Ioo) hpU hval hjet

end SmoothLocal.Taylor

end

end OAI
