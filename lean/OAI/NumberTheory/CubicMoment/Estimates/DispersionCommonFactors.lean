import OAI.NumberTheory.CubicMoment.Estimates.DispersionPoisson

namespace OAI

/-!
# Common factors in the dispersion Poisson identity

The shared Gauss factors cancel before the remaining coprimality condition
is removed by the finite ideal Möbius expansion. The formulas hold even
if a shared factor also divides a residual factor: the character then
vanishes. There is no tacit coprimality assumption on the original pair.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace CubicFirstMoment

/-- The exact surviving character after the Gauss factors cancel. -/
theorem common_gauss_pair_cancellation {k a b : Eisenstein}
    (hk : primary k) (ha : primary a) (hb : primary b)
    (hsk : Squarefree k) (hsa : Squarefree a) (hsb : Squarefree b) :
    gauss (k*a) * star (gauss (k*b)) * (gauss b * star (gauss a)) =
      mixedCubic b a k := by
  have hkg : gauss k * star (gauss k) = 1 := by
    simpa only [ite_eq_left hsk] using gauss_mul_star_squarefree hk
  have hag : gauss a * star (gauss a) = 1 := by
    simpa only [ite_eq_left hsa] using gauss_mul_star_squarefree ha
  have hbg : gauss b * star (gauss b) = 1 := by
    simpa only [ite_eq_left hsb] using gauss_mul_star_squarefree hb
  rw [gauss_mul hk ha, gauss_mul hk hb]
  simp only [star_mul, star_star]
  calc
    _ = (gauss k * star (gauss k)) * (gauss a * star (gauss a)) *
        (gauss b * star (gauss b)) * mixedCubic b a k := by unfold mixedCubic; ring
    _ = _ := by rw [hkg, hag, hbg]; simp

theorem common_amplitude_pair_cancellation {k a b : Eisenstein}
    (hk : primary k) (ha : primary a) (hb : primary b)
    (hsk : Squarefree k) (hsa : Squarefree a) (hsb : Squarefree b)
    (β : Eisenstein → ℂ) (u : ℝ) :
    dispersionAmplitude β u (k*a) * star (dispersionAmplitude β u (k*b)) *
        (gauss b * star (gauss a)) =
      β (k*a) * star (β (k*b)) * normTwist u (k*a) * star (normTwist u (k*b)) *
        mixedCubic b a k := by
  calc
    _ = (β (k*a) * star (β (k*b)) * normTwist u (k*a) * star (normTwist u (k*b))) *
        (gauss (k*a) * star (gauss (k*b)) * (gauss b * star (gauss a))) := by
      simp only [dispersionAmplitude, star_mul]
      ring
    _ = _ := by rw [common_gauss_pair_cancellation hk ha hb hsk hsa hsb]

/-- The existing exact Möbius/Poisson formula applied to a pair with a
shared factor, with all normalized Gauss factors cancelled. -/
theorem dispersion_common_pair_poisson {k a b : Eisenstein}
    (hk : primary k) (ha : primary a) (hb : primary b)
    (hsk : Squarefree k) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    dispersionAmplitude β u (k*a) * star (dispersionAmplitude β u (k*b)) *
      primaryCharacterGram (k*b) (k*a) W A =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        let m := ∏ p ∈ s, p
        β (k*a) * star (β (k*b)) * normTwist u (k*a) * star (normTwist u (k*b)) *
          mixedCubic b a k * (idealMoebius m : ℂ) * mixedCubic b a m *
            (((A / norm m) / (9 * Real.sqrt (norm (b*a)))) : ℝ) *
              ∑' h : Eisenstein, gramDualTerm b a W (A / norm m) h := by
  rw [primaryCharacterGram_common_poisson hk hsk hb ha hsb hsa hab.symm W hW hW' hA,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  dsimp only
  rw [show mixedSymbol b a (∏ p ∈ s, p) = mixedCubic b a (∏ p ∈ s, p) from rfl]
  have hc := common_amplitude_pair_cancellation hk ha hb hsk hsa hsb β u
  linear_combination (idealMoebius (∏ p ∈ s, p) : ℂ) * mixedCubic b a (∏ p ∈ s, p) *
    (((A / norm (∏ p ∈ s, p)) / (9 * Real.sqrt (norm (b*a)))) : ℝ) *
      (∑' h : Eisenstein, gramDualTerm b a W (A / norm (∏ p ∈ s, p)) h) * hc

end CubicFirstMoment

end

end OAI
