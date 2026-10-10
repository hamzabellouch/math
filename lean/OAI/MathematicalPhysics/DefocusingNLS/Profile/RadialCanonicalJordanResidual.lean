import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalModeTail
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalRemainderEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalRemainderEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialJordanSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! The residual of an actual radial Jordan pair is homogeneous and retains finite tail energy. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def canonicalParameterResidualState (ν : ℂ) (Y Z : ℂ → ℝ → E₄)
    (lam : ℂ) (c : ℂ × ℂ) (V : ℝ → E₄) (r : ℝ) : E₄ :=
  V r-canonicalParameterStateCombination ν Y Z lam c r

theorem radialCanonicalJordan_residual (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta lam : ℂ) (hlam : 0≤lam.re) (N : ℕ) (hN : 7≤N)
    (u : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) eta lam)
    (v w : ℝ → ℂ) (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 2 w)
    (he : IsHarmonicRadialSourcePair (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) (radialMatchedProfile n z) eta lam v w u.first u.second)
    (hvt : IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi 0))
    (hwt : IntegrableOn (fun r => r^11*‖iteratedDeriv N w r‖^2) (Ioi 0))
    (hb : ∃ M : ℝ, 0≤M ∧ ∀ r, ‖(v r,w r)‖≤M)
    (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (R : ℝ) (hR : innerBoundaryRadius<R) :
    let ν := radialShootingNu (n+radialInnerShootingThreshold) z
    ∃ c : ℂ × ℂ,
      (∀ r, R≤r → harmonicRadialState u.first u.second r=
        c.1 • spectralPhysicalPair (ν-2*lam) (star ν-2*lam) (Y lam) r+
        c.2 • spectralPhysicalPair (ν-2*lam) (star ν-2*lam) (Z lam) r) ∧
      let W := canonicalParameterResidualState ν Y Z lam c (harmonicRadialState v w)
      (∀ r, R≤r → HasDerivAt W (spectralPhysicalCircularField (ν-2*lam) (star ν-2*lam) eta
        (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r (W r)) r) ∧
      ∃ T : ℝ, R<T ∧ innerBoundaryRadius<T ∧
        ContDiffOn ℝ ∞ (fun r => spectralPhysicalValueMap (W r)) (Ioi T) ∧
        (∃ M : ℝ, 0≤M ∧ ∀ r, T≤r → ‖spectralPhysicalValueMap (W r)‖≤M) ∧
        IntegrableOn (fun r => r^11*‖(iteratedDeriv N (fun s => spectralPhysicalValueMap (W s)) r).1‖^2) (Ioi T) ∧
        IntegrableOn (fun r => r^11*‖(iteratedDeriv N (fun s => spectralPhysicalValueMap (W s)) r).2‖^2) (Ioi T) := by
  intro ν
  have hhalf : -(1/32 : ℝ)≤lam.re := by linarith
  obtain ⟨c,hc⟩ := homogeneous_matched_pair_canonical_tail_from n z hX hz eta N hN lam hhalf
    u.first u.second u.first_c2 u.second_c2 u.equation u.bounded u.first_top u.second_top
    Y Z hY hZ R hR
  refine ⟨c,hc,?_⟩
  let W := canonicalParameterResidualState ν Y Z lam c (harmonicRadialState v w)
  have hν : -2*(radialShootingA n : ℂ)+
      2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)=ν :=
    (radialShootingNu_physical n z).symm
  have hνm : -2*(radialShootingA n : ℂ)-
      2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)=star ν := by
    rw [←hν]
    simp only [star_add,star_mul,star_neg,star_ofNat,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
    ring
  have hWe (r : ℝ) (hr : R≤r) : HasDerivAt W
      (spectralPhysicalCircularField (ν-2*lam) (star ν-2*lam) eta
        (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r (W r)) r := by
    have hri : innerBoundaryRadius<r := hR.trans_le hr
    have hr₀ : 0<r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hri
    have hs := harmonicRadialSourcePair_hasDerivAt (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) v w u.first u.second eta lam hv hw he r hr₀
    simp only [hν,hνm] at hs
    exact radialCanonicalParameter_remainder_hasDerivAt n z hX eta lam Y Z hY hZ c
      (harmonicRadialState v w) (harmonicRadialState u.first u.second r) r hri (hc r hr) hs
  have hvw := harmonicRadialSourcePair_contDiffOn (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
    (radialMatchedProfile n z) v w u.first u.second eta lam hv hw he 0 le_rfl
    (radialMatchedProfile_contDiffOn n z hX hz) u.first_smooth u.second_smooth
  obtain ⟨T,hRT,hiT,hWs,hWb,hWp,hWm⟩ := radialCanonicalParameter_remainder_energy n z hX eta
    Y Z hY hZ lam hlam N hN c R v w hvw.1 hvw.2 hvt hwt hb
  have hvalue : (fun r => spectralPhysicalValueMap (W r))=
      fun r => (v r,w r)-canonicalParameterValueCombination ν Y Z lam c r := by
    funext r
    change spectralPhysicalValueMap
      (harmonicRadialState v w r-canonicalParameterStateCombination ν Y Z lam c r)=_
    rw [map_sub,canonicalParameterStateCombination_value]
    rfl
  rw [←hvalue] at hWs hWb hWp hWm
  exact ⟨hWe,T,hRT,hiT,hWs,hWb,hWp,hWm⟩

end DefocusingNLS

end OAI
