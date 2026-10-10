import OAI.NumberTheory.TwoPoint.Bounds.ConditionalComplexCore
import OAI.NumberTheory.TwoPoint.Bounds.PositiveNormalization
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionDeduction

namespace OAI

/-! Theorem 1.2 and Corollary 1.3 of the manuscript, conditionally on the
explicit published short-sum, prime-distribution and circuit inputs. -/

namespace TwoPointCorrelations

theorem conditional_unshiftedCorrectedElliott (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) : UnshiftedCorrectedElliott := by
  intro f g hfm hgm hf hg hnp h hh
  have hnp' : UniformlyNonpretentious (positiveNormalization f) ∨
      UniformlyNonpretentious (positiveNormalization g) :=
    hnp.imp (fun hn => hn.positiveNormalization hf) (fun hn => hn.positiveNormalization hg)
  have hc := conditional_complex_positive_core hP hBr hM hMRT
    hfm.positiveNormalization hgm.positiveNormalization
    (positiveNormalization_norm hf) (positiveNormalization_norm hg) hnp' h hh
  simpa only [positiveNormalization_prefix, correlationSum_eq_positivePrefix] using hc

theorem conditional_binaryCorrectedElliott (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) : BinaryCorrectedElliott :=
  (conditional_unshiftedCorrectedElliott hP hBr hM hMRT).binary

theorem conditional_affineCorrectedElliott (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) : AffineCorrectedElliott :=
  (conditional_binaryCorrectedElliott hP hBr hM hMRT).affine

end TwoPointCorrelations

end OAI
