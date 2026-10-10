import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialModeMatchingZero
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalAnalytic

namespace OAI

/-! Constructed analytic matching data for the actual finite-power profile. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

structure RadialMatchingData (n : ℕ) (z : ProfileMatchingBall) (ell : ℕ) (R L : ℝ) where
  radius_gt : innerBoundaryRadius<R
  regularPlus : ℂ → ℝ → E₄
  regularMinus : ℂ → ℝ → E₄
  outgoingPlus : ℂ → ℝ → E₄
  outgoingMinus : ℂ → ℝ → E₄
  plus_canonical : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
    ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
    (Real.log innerBoundaryRadius) (1,0) outgoingPlus
  minus_canonical : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
    ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
    (Real.log innerBoundaryRadius) (0,1) outgoingMinus
  plus_equation : ∀ lam, ‖lam‖≤L → ∀ r ∈ Ioc 0 R, HasDerivAt (regularPlus lam)
    (spectralPhysicalCircularField
      (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
      (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam)
      ((ell*(ell+10) : ℕ) : ℂ) (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z r) r (regularPlus lam r)) r
  minus_equation : ∀ lam, ‖lam‖≤L → ∀ r ∈ Ioc 0 R, HasDerivAt (regularMinus lam)
    (spectralPhysicalCircularField
      (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
      (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam)
      ((ell*(ell+10) : ℕ) : ℂ) (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z r) r (regularMinus lam r)) r
  regular_rank : ∀ lam, ‖lam‖≤L → LinearIndependent ℂ ![regularPlus lam R,regularMinus lam R]
  regular_c2 : ∀ lam,
    ContDiff ℝ 2 (fun r => (regularPlus lam r).1.1) ∧
    ContDiff ℝ 2 (fun r => (regularPlus lam r).2.1) ∧
    ContDiff ℝ 2 (fun r => (regularMinus lam r).1.1) ∧
    ContDiff ℝ 2 (fun r => (regularMinus lam r).2.1)
  regular_analytic : ∀ lam, ‖lam‖≤L →
    AnalyticAt ℂ (fun w => regularPlus w R) lam ∧ AnalyticAt ℂ (fun w => regularMinus w R) lam

theorem radialMatchingData_nonempty (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (ell : ℕ) (R L : ℝ)
    (hR : innerBoundaryRadius<R) (hL : 0≤L) : Nonempty (RadialMatchingData n z ell R L) := by
  let m := n+radialInnerShootingThreshold
  let nu := radialShootingNu m z
  let eta : ℂ := ((ell*(ell+10) : ℕ) : ℂ)
  have hR0 : 0<R := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hR
  obtain ⟨Rp,Rm,hp,hm,hr,hc,ha,_⟩ := exists_regular_physical_basis_c2 ell m nu (star nu)
    R L hR0 hL (radialMatchedEvenProfile n z) (radialMatchedEvenProfile_contDiff n z hX hz).continuous
  have hm1 : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  obtain ⟨Yp,hYp⟩ := canonical_holomorphic_circular_allOrders nu nu (star nu) eta
    (radialShootingM z) m hm1 (Real.log innerBoundaryRadius) hX (radialShootingM_ne_zero z) (1,0)
  obtain ⟨Ym,hYm⟩ := canonical_holomorphic_circular_allOrders nu nu (star nu) eta
    (radialShootingM z) m hm1 (Real.log innerBoundaryRadius) hX (radialShootingM_ne_zero z) (0,1)
  exact ⟨⟨hR,Rp,Rm,Yp,Ym,hYp,hYm,hp,hm,hr,hc,fun lam hl => ha lam hl R hR0.le⟩⟩

noncomputable def RadialMatchingData.determinant {n ell : ℕ} {z : ProfileMatchingBall} {R L : ℝ}
    (d : RadialMatchingData n z ell R L) (lam : ℂ) : ℂ :=
  spectralMatchingDeterminant (d.regularPlus lam R) (d.regularMinus lam R)
    (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
      (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (d.outgoingPlus lam) R)
    (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
      (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (d.outgoingMinus lam) R)

theorem RadialMatchingData.determinant_analyticAt {n ell : ℕ} {z : ProfileMatchingBall} {R L : ℝ}
    (d : RadialMatchingData n z ell R L) (lam : ℂ) (hlam : ‖lam‖≤L) :
    AnalyticAt ℂ d.determinant lam := by
  have hR1 : 1≤R := innerBoundaryRadius_bounds.1.trans d.radius_gt.le
  have ha (Y : ℂ → ℝ → E₄)
      (hY : ∀ w t, 0≤t → AnalyticAt ℂ (fun v => Y v t) w) :
      AnalyticAt ℂ (fun w => spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*w)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*w) (Y w) R) lam := by
    apply spectralPhysicalPair_analyticAt
    · fun_prop
    · fun_prop
    · exact hY lam (Real.log R) (Real.log_nonneg hR1)
  exact spectralMatchingDeterminant_analyticAt _ _ _ _ lam
    (d.regular_analytic lam hlam).1 (d.regular_analytic lam hlam).2
    (ha d.outgoingPlus d.plus_canonical.2.2.1) (ha d.outgoingMinus d.minus_canonical.2.2.1)

theorem RadialMatchingData.mode_zero {n ell N : ℕ} {z : ProfileMatchingBall} {R L : ℝ}
    (d : RadialMatchingData n z ell R L)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (hN : 7≤N) (lam : ℂ) (hlam : ‖lam‖≤L)
    (hhalf : -(1/32 : ℝ)≤lam.re)
    (u : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
      (radialMatchedProfile n z) ((ell*(ell+10) : ℕ) : ℂ) lam) : d.determinant lam=0 := by
  have heta : (((ell*(ell+10) : ℕ) : ℝ) : ℂ)=((ell*(ell+10) : ℕ) : ℂ) := by norm_cast
  have hu : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
      (radialMatchedProfile n z) (((ell*(ell+10) : ℕ) : ℝ) : ℂ) lam := by
    simpa only [heta] using u
  have h := radialMatched_mode_matching_zero n N z hX hz hN ((ell*(ell+10) : ℕ) : ℝ)
    (by positivity) lam hhalf hu R d.radius_gt (d.regularPlus lam) (d.regularMinus lam)
    ⟨(d.regular_c2 lam).1,(d.regular_c2 lam).2.1⟩
    ⟨(d.regular_c2 lam).2.2.1,(d.regular_c2 lam).2.2.2⟩
    (by simpa only [heta] using d.plus_equation lam hlam)
    (by simpa only [heta] using d.minus_equation lam hlam)
    (d.regular_rank lam hlam) d.outgoingPlus d.outgoingMinus
    (by simpa only [heta] using d.plus_canonical)
    (by simpa only [heta] using d.minus_canonical)
  exact h

end DefocusingNLS

end OAI
