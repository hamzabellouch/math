import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularPhysical

namespace OAI

/-! Restoring the angular power in a forced regular equation. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralRegularPhysical_source_hasDerivAt (ell m : ℕ) (νp νm Q F G : ℂ)
    (Y : ℝ → E₄) (r : ℝ) (hr : 0 < r)
    (hY : HasDerivAt Y
      (spectralRegularField (2 * ell + 11)
        (spectralDiagonalCoefficient m Q) (spectralCrossCoefficient m Q)
        (-Complex.I * νp / 2 + Complex.I * (ell : ℂ) / 2)
        (Complex.I * νm / 2 - Complex.I * (ell : ℂ) / 2) r (Y r) +
        ((0, F), (0, G))) r) :
    HasDerivAt (spectralAngularPair ell Y)
      (spectralPhysicalCircularField νp νm ((ell * (ell + 10) : ℕ) : ℂ) m Q r
        (spectralAngularPair ell Y r) +
        ((0, (r : ℂ) ^ ell * F), (0, (r : ℂ) ^ ell * G))) r := by
  let cp := -Complex.I * νp / 2 + Complex.I * (ell : ℂ) / 2
  let cm := Complex.I * νm / 2 - Complex.I * (ell : ℂ) / 2
  let Fp := spectralDiagonalCoefficient m Q * (Y r).1.1 +
    spectralCrossCoefficient m Q * (Y r).2.1 + F
  let Fm := star (spectralCrossCoefficient m Q) * (Y r).1.1 +
    star (spectralDiagonalCoefficient m Q) * (Y r).2.1 + G
  have hp : HasDerivAt (fun t => (Y t).1) ((Y r).1.2,
      -(((2 * ell + 11 : ℕ) : ℂ) / (r : ℂ) + (1 : ℂ) * Complex.I * (r : ℂ) / 2) *
        (Y r).1.2 - cp * (Y r).1.1 + Fp) r := by
    apply ((ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt r hY).congr_deriv
    simp only [ContinuousLinearMap.coe_fst']
    apply Prod.ext
    · simp [spectralRegularField]
    · dsimp only [spectralRegularField, cp, Fp, Prod.fst_add, Prod.snd_add]
      ring
  have hm : HasDerivAt (fun t => (Y t).2) ((Y r).2.2,
      -(((2 * ell + 11 : ℕ) : ℂ) / (r : ℂ) + (-1 : ℂ) * Complex.I * (r : ℂ) / 2) *
        (Y r).2.2 - cm * (Y r).2.1 + Fm) r := by
    apply ((ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt r hY).congr_deriv
    simp only [ContinuousLinearMap.coe_snd']
    apply Prod.ext
    · simp [spectralRegularField]
    · dsimp only [spectralRegularField, cm, Fm, Prod.fst_add, Prod.snd_add]
      ring
  have hdp := spectralAngularJet_hasDerivAt ell 1 cp Fp (fun t => (Y t).1) r hr.ne' hp
  have hdm := spectralAngularJet_hasDerivAt ell (-1) cm Fm (fun t => (Y t).2) r hr.ne' hm
  apply (hdp.prodMk hdm).congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · simp only [Prod.fst_add, add_zero]
    rfl
  · dsimp only [spectralAngularPair, spectralAngularJet, spectralPhysicalCircularField,
      cp, Fp, Prod.fst_add, Prod.snd_add]
    ring
  · simp only [Prod.snd_add, Prod.fst_add, add_zero]
    rfl
  · dsimp only [spectralAngularPair, spectralAngularJet, spectralPhysicalCircularField,
      cm, Fm, Prod.fst_add, Prod.snd_add]
    ring

end DefocusingNLS

end OAI
