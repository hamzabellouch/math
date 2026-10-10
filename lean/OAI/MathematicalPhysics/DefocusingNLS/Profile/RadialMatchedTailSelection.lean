import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailOutgoingSelection

namespace OAI

/-! The actual canonical outgoing plane is selected using only regularity and energy on a tail. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "V" => ℂ × ℂ
local notation "V₄" => V × V
local notation "End" => V →L[ℂ] V

theorem radialMatched_state_canonical_tail_span
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℂ) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hhalf : -(1 / 32 : ℝ) ≤ lam.re)
    (Z : ℝ → V₄) (R₀ : ℝ) (hinner₀ : innerBoundaryRadius<R₀)
    (hZeq : ∀ r, R₀≤r → HasDerivAt Z
      (spectralPhysicalCircularField
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam)
        eta (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r (Z r)) r)
    (hUs : ContDiffOn ℝ ∞ (fun r => spectralPhysicalValueMap (Z r)) (Ioi R₀))
    (hbounded : ∃ M : ℝ, 0≤M ∧ ∀ r, R₀≤r → ‖spectralPhysicalValueMap (Z r)‖≤M)
    (hL2p : IntegrableOn (fun r => r^11*
      ‖(iteratedDeriv N (fun s => spectralPhysicalValueMap (Z s)) r).1‖^2) (Ioi R₀))
    (hL2m : IntegrableOn (fun r => r^11*
      ‖(iteratedDeriv N (fun s => spectralPhysicalValueMap (Z s)) r).2‖^2) (Ioi R₀))
    (Yp Ym : ℂ → ℝ → V₄)
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1, 0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0, 1) Ym)
    (R : ℝ) (hR : R₀ ≤ R) :
    ∃ a : V, Z R =
      a.1 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Yp lam) R +
      a.2 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Ym lam) R := by
  let m := n + radialInnerShootingThreshold
  let ν := radialShootingNu m z
  let νp := ν - 2 * lam
  let νm := star ν - 2 * lam
  let b := radialShootingB (profileMatchingParameter z)
  let q := fun t => (radialExteriorCanonical ν m (radialShootingM z)
    (Real.log innerBoundaryRadius) t).1
  let Q := fun r => Complex.exp (ν * (Real.log r : ℂ)) * q (Real.log r)
  let Zp := spectralPhysicalPair νp νm (Yp lam)
  let Zm := spectralPhysicalPair νp νm (Ym lam)
  let k := N - 1
  have hm : 1 ≤ m := by
    exact Nat.one_le_iff_ne_zero.mpr (radialShootingInner_power_pos n
      (profileMatchingParameter z)).ne'
  have hkn : k + 1 = N := by dsimp only [k]; omega
  have hinner : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
  have hR₀ : 0 < R₀ := lt_trans hinner hinner₀
  have h₀R : R₀ ≤ R := hR
  have hνform : ν = -1 / (m : ℂ) + 2 * Complex.I * (b : ℂ) := by
    dsimp only [ν, b, m]
    unfold radialShootingNu radialShootingQ
    ring
  have hνphysical : ν = -2 * (radialShootingA n : ℂ) + 2 * Complex.I * (b : ℂ) :=
    radialShootingNu_physical n z
  have hνre : ν.re = -2 * radialShootingA n := by
    rw [hνphysical]
    simp [Complex.mul_re, Complex.mul_im]
  have hsame : νp.re = νm.re := by simp [νp, νm, Complex.sub_re]
  have hνweight : 2 * (m : ℝ) * ν.re = -2 := by
    rw [hνre]
    have ha := radialShootingA_power n (profileMatchingParameter z)
    change 2 * radialShootingA n * (m : ℝ) = 1 at ha
    nlinarith
  have hQeq (r : ℝ) (hr : R₀ ≤ r) : Q r = radialMatchedProfile n z r := by
    have hri : innerBoundaryRadius < r := hinner₀.trans_le hr
    simp only [radialMatchedProfile, ite_eq_right hri.not_ge,
      radialShootingExteriorProfile, radialPhysicalExterior, Q, q, ν, m]
  have hQlog (t : ℝ) : Q (Real.exp t) = Complex.exp (ν * (t : ℂ)) * q t := by
    simp only [Q, Real.log_exp]
  have hZ (r : ℝ) (hr : R₀≤r) : HasDerivAt Z
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Z r)) r := by
    rw [hQeq r hr]
    exact hZeq r hr
  have hZp : ∀ r, R₀ ≤ r → HasDerivAt Zp
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zp r)) r := by
    intro r hr
    have hh := spectralPhysicalPair_hasDerivAt ν lam eta m hm q (Yp lam) r (hR₀.trans_le hr)
    apply hh
    · rw [hνform]
      exact spectralPhysicalFactor_scale m (by omega) b r (hR₀.trans_le hr)
    · exact hYp.1 lam (Real.log r) (Real.log_nonneg
        (le_trans (by linarith [innerBoundaryRadius_bounds.1]) (hinner₀.le.trans hr)))
  have hZm : ∀ r, R₀ ≤ r → HasDerivAt Zm
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zm r)) r := by
    intro r hr
    apply spectralPhysicalPair_hasDerivAt ν lam eta m hm q (Ym lam) r (hR₀.trans_le hr)
    · rw [hνform]
      exact spectralPhysicalFactor_scale m (by omega) b r (hR₀.trans_le hr)
    · exact hYm.1 lam (Real.log r) (Real.log_nonneg
        (le_trans (by linarith [innerBoundaryRadius_bounds.1]) (hinner₀.le.trans hr)))
  let C := homogeneousLogRadialStiffness νp νm eta m (fun t => Q (Real.exp t))
  have hCeq : C = homogeneousLogRadialStiffness νp νm eta m
      (fun t => Complex.exp (ν * (t : ℂ)) * q t) := by
    dsimp only [C]
    congr 1
    exact funext hQlog
  have hCb := homogeneousLogRadialStiffness_bound νp νm eta m hm ν.re hνweight _
    (homogeneousPhysicalProfile_logJetBound ν q
      (radialExteriorCanonical_logJetBound ν (radialShootingM z) m
        (Real.log innerBoundaryRadius) hX (radialShootingM_ne_zero z)))
  obtain ⟨LC, hCs⟩ := hCb.smooth
  obtain ⟨LB, hBs⟩ := (((HasLogJetBound.const (10 : End)).mono (by norm_num : (0 : ℝ) ≤ 2)).add
    (HasLogJetBound.exponential 2 homogeneousLogFastDiagonal)).smooth
  let L := max (max LC LB) (Real.log R₀)
  have hB : ContDiffOn ℝ ∞ homogeneousLogRadialDamping (Ioi L) := by
    exact hBs.mono (Ioi_subset_Ioi ((le_max_right LC LB).trans (le_max_left _ _)))
  have hC : ContDiffOn ℝ ∞ C (Ioi L) := by
    rw [hCeq]
    exact hCs.mono (Ioi_subset_Ioi ((le_max_left LC LB).trans (le_max_left _ _)))
  have hrow := homogeneousCanonicalEulerRows_norm_lower ν νp νm eta (radialShootingM z)
    m k hm hνweight (Real.log innerBoundaryRadius) hX (radialShootingM_ne_zero z)
  rw [← hCeq] at hrow
  have hest := homogeneous_canonical_outgoing_log_estimates ν νp νm eta (radialShootingM z)
    m (Real.log innerBoundaryRadius) hX hsame (Yp lam) (Ym lam)
    (hYp.1 lam) (hYm.1 lam) (hYp.2.1 lam) (hYm.2.1 lam)
    (hYp.2.2.2 lam) (hYm.2.2.2 lam)
  let Fp := homogeneousPhysicalLogColumn νp νm (fun t => (Yp lam t).1.1)
    (fun t => (Yp lam t).2.1)
  let Fm := homogeneousPhysicalLogColumn νp νm (fun t => (Ym lam t).1.1)
    (fun t => (Ym lam t).2.1)
  have hvalp : (fun t => spectralPhysicalValueMap (Zp (Real.exp t))) = Fp := by
    funext t
    simp only [Zp, homogeneousPhysicalColumn_logValue, Real.log_exp, Fp]
  have hvalm : (fun t => spectralPhysicalValueMap (Zm (Real.exp t))) = Fm := by
    funext t
    simp only [Zm, homogeneousPhysicalColumn_logValue, Real.log_exp, Fm]
  dsimp only [Fp] at hvalp
  dsimp only [Fm] at hvalm
  have hrem := hest.1 (k + 1)
  rw [← hvalp, ← hvalm] at hrem
  obtain ⟨M, hM, hMb⟩ := hest.2
  have hscaled := homogeneousLogRobin_error_to_radial _ (homogeneousDiagonal νp νm) M hMb
  have herr : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ r in atTop,
      ‖spectralJetRobin (Zp r) (Zm r) - r⁻¹ • homogeneousDiagonal νp νm‖ ≤ M / r ^ 3 := by
    refine ⟨M, hM, ?_⟩
    filter_upwards [hscaled, eventually_ge_atTop (1 : ℝ)] with r hr hr1
    have hp := homogeneousCircularValue_derivatives νp νm eta (q (Real.log r)) m
      (Yp lam) (Real.log r) (hYp.1 lam (Real.log r) (Real.log_nonneg hr1))
    have hm' := homogeneousCircularValue_derivatives νp νm eta (q (Real.log r)) m
      (Ym lam) (Real.log r) (hYm.1 lam (Real.log r) (Real.log_nonneg hr1))
    rw [spectralJetRobin, homogeneousPhysicalColumn_robin νp νm (Yp lam) (Ym lam)
      r hp.1 hp.2 hm'.1 hm'.2]
    exact hr
  have hbeta : -6 < (k : ℝ) - (11 + νp.re) := by
    have hh := fast_derivative_exponent (radialShootingA n) lam.re N
      (by unfold radialShootingA; positivity) hhalf hN
    have hkreal : (k : ℝ) + 1 = N := by exact_mod_cast hkn
    have hre : νp.re = -2 * radialShootingA n - 2 * lam.re := by
      change (ν - 2 * lam).re = _
      rw [Complex.sub_re, Complex.mul_re, hνre]
      norm_num
    rw [hre]
    linarith
  have hL2p' : IntegrableOn (fun r => r^11*
      ‖(iteratedDeriv (k+1) (fun s => spectralPhysicalValueMap (Z s)) r).1‖^2) (Ioi R₀) := by
    simpa only [hkn] using hL2p
  have hL2m' : IntegrableOn (fun r => r^11*
      ‖(iteratedDeriv (k+1) (fun s => spectralPhysicalValueMap (Z s)) r).2‖^2) (Ioi R₀) := by
    simpa only [hkn] using hL2m
  apply homogeneousPhysicalOutgoing_tail_selection νp νm eta m k Q
    Z Zp Zm R₀ L ((1 / 2 : ℝ) ^ k / 2)
    hR₀ (le_max_right _ _) (by positivity) hsame hbeta.le
    (by have hk7 : (7 : ℝ) ≤ N := by exact_mod_cast hN
        have hkreal : (k : ℝ) + 1 = N := by exact_mod_cast hkn
        push_cast
        linarith) _ hZ hZp hZm hUs hbounded hL2p' hL2m' hB hC hrow hrem herr R h₀R
  exact (radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono
    (fun _ hr => hR₀.trans_le hr) |>.congr (fun r hr => hQeq r hr)

end DefocusingNLS

end OAI
