import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCouplingEstimate
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationPotential

namespace OAI

/-! The small coefficient in the shell Green argument is supplied by the
actual matched profile, uniformly in both spectral and angular parameters. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def spectralShellPlusForcing (m : ℕ) (Q : ℂ) (r : ℝ)
    (u : (ℂ × ℂ) × (ℂ × ℂ)) : ℂ :=
  spectralDiagonalCoefficient m Q*u.1.1+
    spectralCrossCoefficient m Q*(homogeneousSpectralLocalizationFactor 1 r/
      homogeneousSpectralLocalizationFactor (-1) r)*u.2.1

noncomputable def spectralShellMinusForcing (m : ℕ) (Q : ℂ) (r : ℝ)
    (u : (ℂ × ℂ) × (ℂ × ℂ)) : ℂ :=
  star (spectralDiagonalCoefficient m Q)*u.2.1+
    star (spectralCrossCoefficient m Q)*(homogeneousSpectralLocalizationFactor (-1) r/
      homogeneousSpectralLocalizationFactor 1 r)*u.1.1

theorem spectralShellForcing_bound (m : ℕ) (Q : ℂ) (r kp km k C : ℝ)
    (hr : 0<r) (hk : 0<k) (hkp : k≤ kp) (hkm : k≤ km)
    (u : (ℂ × ℂ) × (ℂ × ℂ))
    (hcoef : ‖spectralDiagonalCoefficient m Q‖+‖spectralCrossCoefficient m Q‖≤ C/r^2) :
    ‖spectralShellPlusForcing m Q r u‖≤ C/(k*r^2)*spectralShellPairNorm kp km u ∧
    ‖spectralShellMinusForcing m Q r u‖≤ C/(k*r^2)*spectralShellPairNorm kp km u := by
  obtain ⟨hp,hm⟩ := spectralShellPairNorm_values kp km k hk hkp hkm u
  have hN := spectralShellPairNorm_nonneg kp km (hk.trans_le hkp).le u
  have hcoef0 : 0 ≤ C/r^2 := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hcoef
  have hmax : max ‖u.1.1‖ ‖u.2.1‖≤ spectralShellPairNorm kp km u/k := max_le hp hm
  have hbound : (‖spectralDiagonalCoefficient m Q‖+‖spectralCrossCoefficient m Q‖)*
      max ‖u.1.1‖ ‖u.2.1‖≤ C/(k*r^2)*spectralShellPairNorm kp km u := by
    calc
      _ ≤ (C/r^2)*(spectralShellPairNorm kp km u/k) := by gcongr
      _ = _ := by ring
  constructor
  · exact (homogeneousSpectralLocalization_coupling_bound 1 r hr
      (spectralDiagonalCoefficient m Q) (spectralCrossCoefficient m Q) u.1.1 u.2.1).trans hbound
  · have hh := homogeneousSpectralLocalization_coupling_bound (-1) r hr
      (star (spectralDiagonalCoefficient m Q)) (star (spectralCrossCoefficient m Q)) u.2.1 u.1.1
    simpa only [spectralShellMinusForcing,norm_star,neg_neg,max_comm] using hh.trans (by simpa only [norm_star,max_comm] using hbound)

theorem radialMatched_shell_forcing_bound (C : ℝ) (hC : 0<C) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall, ∀ r kp km k : ℝ,
      innerBoundaryRadius<r → 0<k → k≤ kp → k≤ km →
      ∀ u : (ℂ × ℂ) × (ℂ × ℂ),
      ‖spectralShellPlusForcing (n+radialInnerShootingThreshold)
        (radialMatchedProfile n z r) r u‖≤ C/(k*r^2)*spectralShellPairNorm kp km u ∧
      ‖spectralShellMinusForcing (n+radialInnerShootingThreshold)
        (radialMatchedProfile n z r) r u‖≤ C/(k*r^2)*spectralShellPairNorm kp km u := by
  filter_upwards [homogeneousSpectralLocalization_uniform_potential C hC] with n hn
  intro z r kp km k hr hk hp hm u
  have hr0 : 0<r := by linarith [innerBoundaryRadius_bounds.1]
  apply spectralShellForcing_bound (n+radialInnerShootingThreshold)
    (radialMatchedProfile n z r) r kp km k C hr0 hk hp hm u
  exact (le_div_iff₀ (sq_pos_of_pos hr0)).mpr (by simpa only [mul_comm] using (hn z r hr).le)

end DefocusingNLS

end OAI
