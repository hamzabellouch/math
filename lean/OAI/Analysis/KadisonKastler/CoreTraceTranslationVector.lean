import OAI.Analysis.KadisonKastler.RegularReflectedGauge
import OAI.Analysis.KadisonKastler.RegularCoreConjugateGenerators

namespace OAI

/-! # Trace-vector symmetry for the translation generators -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hJU : ∀ s x, J ((U s : H →L[ℂ] H) x) = (U s : H →L[ℂ] H) (J x))
  (Ω : H) (hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω) (hJΩ : J Ω = Ω)

include hΩ in
theorem regularCoreAction_traceVector (s : Multiplicative ℝ) :
    (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) =
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) := by
  change (regularConstantHom volume (U s : H →L[ℂ] H) *
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) = _
  rw [(regularConstant_commute_translation (U s : H →L[ℂ] H) s).eq]
  change (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularConstantHom volume (U s : H →L[ℂ] H)
      (regularFrequencyPacket coreTraceFrequencyScalar Ω)) = _
  rw [regularConstantHom_frequencyPacket, hΩ]
  rfl

include hJ hJU hΩ hJΩ in
theorem coreTraceTranslation_vector_symmetry (s : Multiplicative ℝ) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) =
    regularCoreConjugation U hU J
      ((star (regularRightTranslation (H := H) s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (coreTraceFrequencyVector Ω)) := by
  have hCξ := regularCoreConjugation_traceVector_fixed U hU J Ω hΩ hJΩ
  have hc := congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    T (coreTraceFrequencyVector Ω))
    (regularCoreConjugation_translation U hU J hJU hJ (-s.toAdd))
  have hs : (regularRightTranslation (H := H) (Multiplicative.ofAdd (-s.toAdd)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (star (regularRightTranslation (H := H) s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    exact congrArg Subtype.val (regularGroup_star_eq (regularRightTranslation (H := H)) s.toAdd).symm
  rw [hs] at hc
  change regularCoreConjugation U hU J
    ((star (regularRightTranslation (H := H) s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCoreConjugation U hU J (coreTraceFrequencyVector Ω))) = _ at hc
  rw [hCξ] at hc
  simpa only [neg_neg, ofAdd_toAdd, regularCoreAction_traceVector U Ω hΩ] using hc.symm

end

end KadisonKastler

end OAI
