import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularFluxSign

namespace OAI

/-! The negative outgoing flux propagates across the corner and the initial arc. -/

open Set
namespace DefocusingNLS

theorem highAngular_actualFlux_join (q : ℂ) (M : ℕ) (Z h : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hZ : 2704/1000 ≤ Z) :
    highRayActualFlux q M Z h 0-highArcActualFlux q M Z h (highArcAngle/2) =
      (highRayCorrection 0-highArcCorrection Z (highArcAngle/2))*
        Complex.normSq (highRayWave q M Z h 0) := by
  have ha : 0 ≤ highArcAngle := Real.arccos_nonneg _
  have hj := highContour_join Z h
  have hU : highArcWave q M Z h (highArcAngle/2)=highRayWave q M Z h 0 := by
    dsimp only [highArcWave,highRayWave]
    rw [hj.1]
  have hD : deriv (highArcWave q M Z h) (highArcAngle/2)=deriv (highRayWave q M Z h) 0 := by
    rw [highArcWave_deriv q M Z h _ hq hh hZ (by linarith) (by linarith),
      highRayWave_deriv q M Z h 0 hq le_rfl,hj.1,hj.2]
  unfold highRayActualFlux highArcActualFlux highAngularFlux
  dsimp only
  rw [hU,hD,hj.1,hj.2]
  ring

theorem highArcActualFlux_monotoneOn (q : ℂ) (M : ℕ) (Z h : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1)
    (hσ : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-q).re) (hZ : 2704/1000 ≤ Z) :
    MonotoneOn (highArcActualFlux q M Z h) (Icc 0 (highArcAngle/2)) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 (highArcAngle/2)) :=
    hasDerivAt_highArcActualFlux q M Z h t hq hh hZ (by linarith [ht.1]) (by linarith [ht.2])
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (highArcAngle/2))
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have hti := interior_subset ht
    rw [(hd t hti).deriv]
    have hgeo := highArc_geometry Z (2*t) hZ (by linarith [hti.1]) (by linarith [hti.2])
    have hV := highArcPotential_pos _ (M : ℝ) Z (2*t) hσ hZ
      (by linarith [hti.1]) (by linarith [hti.2])
    exact add_nonneg (mul_nonneg hgeo.2.2.1 (Complex.normSq_nonneg _))
      (mul_nonneg hV.le (Complex.normSq_nonneg _))

theorem highArcActualFlux_initial_neg (q : ℂ) (M : ℕ) (Z h : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hM : 9 ≤ M)
    (hσ : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-q).re)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    highArcActualFlux q M Z h 0 < 0 := by
  have ha : 0 ≤ highArcAngle/2 := div_nonneg (Real.arccos_nonneg _) (by norm_num)
  have hmono := highArcActualFlux_monotoneOn q M Z h hq hh hσ hZ
    (show (0 : ℝ) ∈ Icc 0 (highArcAngle/2) from ⟨le_rfl,ha⟩)
    (show highArcAngle/2 ∈ Icc 0 (highArcAngle/2) from ⟨ha,le_rfl⟩) ha
  have hjump : 0 ≤ highRayActualFlux q M Z h 0-highArcActualFlux q M Z h (highArcAngle/2) := by
    rw [highAngular_actualFlux_join q M Z h hq hh hZ]
    exact mul_nonneg (highCorrection_join Z hZ hZ').le (Complex.normSq_nonneg _)
  have hneg := highRayActualFlux_initial_neg q M Z h hq hh hM hσ hZ hZ'
  linarith

end DefocusingNLS

end OAI
