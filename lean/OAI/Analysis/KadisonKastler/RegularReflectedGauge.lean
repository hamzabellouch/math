import OAI.Analysis.KadisonKastler.CoreTraceReflectedPackets
import OAI.Analysis.KadisonKastler.RegularCoreConjugation
import OAI.Analysis.KadisonKastler.RegularActionPackets

namespace OAI

/-! # Gauge identities for the reflected modular conjugation -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H)

theorem regularReflectedConjugation_gauge_star
    (hJU : ∀ s x, J ((U s : H →L[ℂ] H) x) = (U s : H →L[ℂ] H) (J x))
    (f : RegularCoreHilbert H) :
    regularReflectedConjugation J
      ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
    (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularReflectedConjugation J f) := by
  apply Lp.ext
  filter_upwards [regularReflectedConjugation_apply_ae J
      ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularGauge_star_apply_ae U hU f),
    regularGauge_apply_ae U hU (regularReflectedConjugation J f),
    regularReflectedConjugation_apply_ae J f] with t hD hG hR hF
  simp only [Function.comp_def] at hG
  rw [hD, hG, hR, hF]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t), neg_neg]
  exact hJU _ _

theorem regularCoreEmbedding_packet_fixed (Ω : H)
    (hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω) (a : H →L[ℂ] H)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    regularCoreEmbedding U hU a (regularFrequencyPacket φ Ω) =
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyPacket φ (a Ω)) := by
  change (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU)))
    (regularConstantHom volume a) (regularFrequencyPacket φ Ω) = _
  rw [Unitary.conjStarAlgAut_star_apply]
  change (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularConstantHom volume a
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyPacket φ Ω))) = _
  rw [regularGauge_frequencyPacket_fixed U hU Ω hΩ, regularConstantHom_frequencyPacket]

theorem regularCoreConjugation_traceVector_fixed (Ω : H)
    (hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω) (hJΩ : J Ω = Ω) :
    regularCoreConjugation U hU J (coreTraceFrequencyVector Ω) = coreTraceFrequencyVector Ω := by
  change (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularReflectedConjugation J (regularFrequencyPacket coreTraceFrequencyScalar Ω)) = _
  rw [regularReflectedConjugation_real_packet J _ coreTraceFrequencyScalar_real,
    hJΩ, regularGauge_star_frequencyPacket_fixed U hU Ω hΩ]
  rfl

end

end KadisonKastler

end OAI
