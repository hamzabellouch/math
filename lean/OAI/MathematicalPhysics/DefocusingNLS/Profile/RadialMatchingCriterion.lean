import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedMatchingMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSymmetryLocalization

namespace OAI

/-! The actual matching determinant detects full radial modes in the bounded
tail half-plane; its zeros inherit the proved large-power localization. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate

theorem RadialMatchingData.zero_iff_mode {n ell N : ℕ} {z : ProfileMatchingBall} {R L : ℝ}
    (d : RadialMatchingData n z ell R L)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (hN : 7 ≤ N)
    (lam : ℂ) (hlam : ‖lam‖ ≤ L) (htail : -radialShootingA n ≤ lam.re)
    (hhalf : -(1 / 32 : ℝ) ≤ lam.re) :
    d.determinant lam = 0 ↔
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) N
        (radialMatchedProfile n z) ((ell * (ell + 10) : ℕ) : ℂ) lam) := by
  constructor
  · exact homogeneousGlued_matching_mode d hX hz N hN lam hlam htail
  · rintro ⟨u⟩
    exact d.mode_zero hX hz hN lam hlam hhalf u

theorem radialMatching_radial_zeros_localize (hR : RectangleRouche)
    (K : Set ℂ) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (z : ProfileMatchingBall) (R L : ℝ)
      (d : RadialMatchingData n z 0 R L),
      HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z = 0 → ∀ lam ∈ K, ‖lam‖ ≤ L →
      -radialShootingA n ≤ lam.re → d.determinant lam = 0 →
      dist lam 0 < ε ∨ dist lam 1 < ε := by
  have ha := radialShootingA_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))
  filter_upwards [ha, radialMatchedSpectralMode_radial_localization hR 7 (by norm_num)
    K hK ε hε] with n hn hloc z R L d hX hz lam hlam hL htail hzero
  have hu := homogeneousGlued_matching_mode d hX hz 7 (by norm_num) lam hL htail hzero
  apply hloc z hX hz lam hlam (by linarith)
  simpa only [Nat.zero_mul, Nat.cast_zero] using hu

theorem radialMatching_translation_zeros_localize (hR : RectangleRouche)
    (K : Set ℂ) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (z : ProfileMatchingBall) (R L : ℝ)
      (d : RadialMatchingData n z 1 R L),
      HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z = 0 → ∀ lam ∈ K, ‖lam‖ ≤ L →
      -radialShootingA n ≤ lam.re → d.determinant lam = 0 →
      dist lam (1 / 2) < ε := by
  have ha := radialShootingA_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))
  filter_upwards [ha, radialMatchedSpectralMode_translation_localization hR 7 (by norm_num)
    K hK ε hε] with n hn hloc z R L d hX hz lam hlam hL htail hzero
  have hu := homogeneousGlued_matching_mode d hX hz 7 (by norm_num) lam hL htail hzero
  apply hloc z hX hz lam hlam (by linarith)
  norm_num only [Nat.one_mul, Nat.reduceAdd, Nat.cast_ofNat] at hu
  exact hu

end DefocusingNLS

end OAI
