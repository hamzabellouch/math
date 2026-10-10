import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialNonvanishing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! Every nonzero regular radial eigenpair has strictly positive physical
H1/angular energy on every ball of positive radius. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem harmonicRadialEigenpair_energy_pos (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ)
    (eta : ℝ) (lam : ℂ) (heta : 0 ≤ eta) (hQ : ContinuousOn Q (Ioi 0))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (hn : ∃ r : ℝ, 0 < r ∧ (f r ≠ 0 ∨ g r ≠ 0)) (R : ℝ) (hR : 0 < R) :
    0 < ∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta f g r := by
  apply intervalIntegral.integral_pos hR (spectralRadialEnergyDensity_continuous eta f g hf hg).continuousOn
  · intro r hr
    have hr0 := hr.1.le
    dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy]
    positivity
  · obtain ⟨r,hr,hne⟩ := harmonicRadialEigenpair_nonzero_on_ball a b m Q f g (eta : ℂ) lam hQ hf hg he hn R hR
    refine ⟨r,⟨hr.1.le,hr.2⟩,?_⟩
    have hv : 0 < ‖f r‖^2+‖g r‖^2 := by
      rcases hne with hne | hne
      · have hp := sq_pos_of_pos (norm_pos_iff.mpr hne)
        nlinarith [sq_nonneg ‖g r‖]
      · have hp := sq_pos_of_pos (norm_pos_iff.mpr hne)
        nlinarith [sq_nonneg ‖f r‖]
    have hp := mul_pos (pow_pos hr.1 11) hv
    have hr0 := hr.1
    have hder : 0 ≤ r^11*(‖deriv f r‖^2+‖deriv g r‖^2) := by positivity
    have hang : 0 ≤ eta*r^9*(‖f r‖^2+‖g r‖^2) := by positivity
    dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy]
    nlinarith only [hp,hder,hang]

end DefocusingNLS

end OAI
