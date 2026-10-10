import OAI.Analysis.KadisonKastler.ScalarFrequencySwap
import OAI.Analysis.KadisonKastler.CyclicCutSwap
import OAI.Analysis.KadisonKastler.FourierSwapIdentity

namespace OAI

/-! # The Fourier gauge identity on a scalar cyclic spectral space -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

theorem cyclicGauge_fourier (a : ℝ) (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    (𝓕 ((star (modularCyclicGauge J Ω hsep hcyc x) :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x))
      (regularFrequencyProjection a ((modularCyclicGauge J Ω hsep hcyc x :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)) F))) :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x)) =
      modularCyclicCutField M J Ω x a (𝓕 F) := by
  exact fourier_swap_identity (modularCyclicMeasure (M := M) J Ω x)
    ((star (modularCyclicGauge J Ω hsep hcyc x) :
      RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
        RegularCoreHilbert (ModularCyclicSpace M J Ω x)) * regularFrequencyProjection a *
      (modularCyclicGauge J Ω hsep hcyc x :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)))
    (modularCyclicCutField M J Ω x a)
    (shiftedFrequencyField (modularCyclicMeasure (M := M) J Ω x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a)
    (fourierShiftedField (modularCyclicMeasure (M := M) J Ω x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a)
    (cyclicGauge_frequency_swap J Ω hsep hcyc x a)
    (cyclicCutField_swap J Ω hsep hcyc x a)
    (fourierShiftedField_intertwines _ _ _ a) F

theorem cyclicGauge_identity (a : ℝ) :
    (star (modularCyclicGauge J Ω hsep hcyc x) :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)) *
      regularFrequencyProjection a *
      (modularCyclicGauge J Ω hsep hcyc x :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)) =
    (Lp.fourierTransformₗᵢ ℝ (ModularCyclicSpace M J Ω x)).symm.conjStarAlgEquiv
      (modularCyclicCutField M J Ω x a) := by
  exact linearIsometryEquiv_conjugate_of_intertwines
    (Lp.fourierTransformₗᵢ ℝ (ModularCyclicSpace M J Ω x)) _ _
    (cyclicGauge_fourier J Ω hsep hcyc x a)

end

end KadisonKastler

end OAI
