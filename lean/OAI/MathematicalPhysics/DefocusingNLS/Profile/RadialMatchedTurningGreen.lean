import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledGreenFull
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPairWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellForcingContinuity

namespace OAI

/-! Apply the full Green bound to the actual odd-power coefficient field.
For two turning channels the correction is proportional to the sum of the
vanishing turning scales. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_turning_green_small (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∀ R E r A M bp bm eta omega gp gm dp dm : ℝ,
      innerBoundaryRadius < R → r ∈ Icc R E → 0 ≤ A → 0 ≤ M → 0 < dp → 0 < dm →
      let kp := spectralTurningRegularizedWeight 1 bp eta omega gp dp
      let km := spectralTurningRegularizedWeight (-1) bm eta omega gm dm
      ∀ u : ℝ → (ℂ × ℂ) × (ℂ × ℂ), ContinuousOn u (Icc R E) →
      (∀ t ∈ Icc R E, spectralShellPairNorm (kp t) (km t) (u t) ≤ M) →
      ∀ Dp Up Dm Um : ℝ → ℂ × ℂ, ∀ Wp Wm : ℂ,
      ContinuousOn Dp (Icc R E) → ContinuousOn Up (Icc R E) →
      ContinuousOn Dm (Icc R E) → ContinuousOn Um (Icc R E) → Wp ≠ 0 → Wm ≠ 0 →
      spectralScalarWronskian (Dp r) (Up r) = Wp →
      spectralScalarWronskian (Dm r) (Um r) = Wm →
      (∀ t ∈ Icc R E, spectralShellNorm (kp r) (spectralScalarGreenState Dp Up Wp r t) ≤ A/(kp t)) →
      (∀ t ∈ Icc R E, spectralShellNorm (km r) (spectralScalarGreenState Dm Um Wm r t) ≤ A/(km t)) →
      spectralShellPairNorm (kp r) (km r)
        (spectralScalarGreenIntegral R E Dp Up Wp
          (fun t => spectralShellPlusForcing (n+radialInnerShootingThreshold)
            (radialMatchedProfile n z t) t (u t)) r,
        spectralScalarGreenIntegral R E Dm Um Wm
          (fun t => spectralShellMinusForcing (n+radialInnerShootingThreshold)
            (radialMatchedProfile n z t) t (u t)) r) ≤ ((A+1)*C/R)*(dp+dm)*M := by
  filter_upwards [radialMatched_shell_forcing_bound C hC] with n hn
  intro z hX hz R E r A M bp bm eta omega gp gm dp dm hRb hr hA hM hdp hdm kp km
    u hu huM Dp Up Dm Um Wp Wm hDp hUp hDm hUm hWp hWm hdetp hdetm hgp hgm
  let kap := (Real.sqrt (dp+dm))⁻¹
  have hsum : 0 < dp+dm := add_pos hdp hdm
  have hkap : 0 < kap := inv_pos.mpr (Real.sqrt_pos.mpr hsum)
  obtain ⟨hp,hm⟩ := spectralTurning_pair_floor dp dm hdp hdm
  have hkp (t : ℝ) (_ht : t ∈ Icc R E) : kap ≤ kp t :=
    hp.trans (spectralTurning_weight_floor 1 bp eta omega gp dp t)
  have hkm (t : ℝ) (_ht : t ∈ Icc R E) : kap ≤ km t :=
    hm.trans (spectralTurning_weight_floor (-1) bm eta omega gm dm t)
  have hR : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hQ : ContinuousOn (radialMatchedProfile n z) (Icc R E) :=
    (radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono
      (fun t ht => hR.trans_le ht.1)
  have hfc := spectralShellForcing_continuousOn (n+radialInnerShootingThreshold)
    R E hR (radialMatchedProfile n z) u hQ hu
  have hb := spectralCoupledGreen_full_small R E r kap A C M hR hr hkap hA hC.le hM
    kp km hkp hkm Dp Up Dm Um Wp Wm _ _ hDp hUp hDm hUm hfc.1 hfc.2
    hWp hWm hdetp hdetm hgp hgm
    (fun t ht => (hn z t (kp t) (km t) kap (hRb.trans_le ht.1) hkap (hkp t ht) (hkm t ht) (u t)).1.trans
      (mul_le_mul_of_nonneg_left (huM t ht) (by positivity)))
    (fun t ht => (hn z t (kp t) (km t) kap (hRb.trans_le ht.1) hkap (hkp t ht) (hkm t ht) (u t)).2.trans
      (mul_le_mul_of_nonneg_left (huM t ht) (by positivity)))
  apply hb.trans_eq
  dsimp only [kap]
  rw [inv_pow,Real.sq_sqrt hsum.le]
  field_simp

end DefocusingNLS

end OAI
