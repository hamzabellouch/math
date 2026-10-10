import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalEnergy

namespace OAI

/-! The published oscillator gap, specialized to the one-dimensional form.

Gerald Teschl, *Mathematical Methods in Quantum Mechanics*, second edition,
AMS Graduate Studies in Mathematics 157 (2014), Section 8.3, equations
(8.39)--(8.43) and Theorem 8.5; form-domain max-min in Theorem 4.12.
https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe2.pdf

The one-dimensional Hermite calculation gives eigenvalues `(2n+1)freq`
for `-∂²+freq²z²` and the Gaussian (8.41). Dividing by two gives bottom
`freq/2` and gap `freq`. We assume just the resulting projection-form inequality
on compact C¹ tests. The Gaussian and its normalization and attained energy
are actual definitions and proved facts, not extra premises. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def PublishedVerticalOscillatorGap : Prop :=
  ∀ (freq : ℝ), 0 < freq → ∀ (u : ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u →
    (3 * freq / 2) * (∫ z, u z ^ 2) - freq * (∫ z, u z * verticalMode freq z) ^ 2 ≤
      verticalForm freq u

theorem verticalForm_gap_on_orthogonal (hpublished : PublishedVerticalOscillatorGap)
    {freq : ℝ} (hfreq : 0 < freq) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) (ho : (∫ z, u z * verticalMode freq z) = 0) :
    (3 * freq / 2) * (∫ z, u z ^ 2) ≤ verticalForm freq u := by
  simpa only [ho, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero] using
    hpublished freq hfreq u hu hc

end ContinuumCoulomb

end

end OAI
