import OAI.Probability.SLE.Mass.RandomMeasureDifference
import OAI.Probability.SLE.Mass.LevelConditionalMean

namespace OAI

/-! A conditional sum identity identifies the positive remaining measure.
Cancellation uses sigma finiteness, not finite total trace mass. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

lemma bind_add_of_ae
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (μ ν η : Ω → Measure X) (hμ : Measurable μ) (hν : Measurable ν) (hη : Measurable η)
    (hsum : ∀ᵐ ω ∂P, η ω + μ ω = ν ω) : P.bind η + P.bind μ = P.bind ν := by
  apply Measure.ext
  intro A hA
  rw [Measure.add_apply,Measure.bind_apply hA hη.aemeasurable,
    Measure.bind_apply hA hμ.aemeasurable,Measure.bind_apply hA hν.aemeasurable]
  have hηA : Measurable (fun ω => η ω A) := (Measure.measurable_coe hA).comp hη
  rw [← lintegral_add_left hηA]
  apply lintegral_congr_ae
  filter_upwards [hsum] with ω hω
  simpa only [Measure.add_apply] using congrArg (fun ρ : Measure X => ρ A) hω

lemma bind_remainder_eq_of_sum
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (μ ν η : Ω → Measure X) (hμ : Measurable μ) (hν : Measurable ν) (hη : Measurable η)
    [SigmaFinite (P.bind μ)] (K : Measure X)
    (hsum : ∀ᵐ ω ∂P, η ω + μ ω = ν ω)
    (hkernel : P.bind ν = P.bind μ + K) : P.bind η = K := by
  apply (Measure.add_left_inj (P.bind μ) (P.bind η) K).mp
  calc
    P.bind η + P.bind μ = P.bind ν := bind_add_of_ae P μ ν η hμ hν hη hsum
    _ = P.bind μ + K := hkernel
    _ = K + P.bind μ := add_comm _ _


lemma restricted_bind_le_of_ae_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (μ ν : Ω → Measure X) (hμ : Measurable μ) (hν : Measurable ν)
    (hle : ∀ᵐ ω ∂P, μ ω ≤ ν ω) (E : Set Ω) : (P.restrict E).bind μ ≤ P.bind ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA hμ.aemeasurable,Measure.bind_apply hA hν.aemeasurable]
  exact (lintegral_mono_ae ((ae_restrict_of_ae hle).mono (fun ω hω => hω A))).trans
    (lintegral_mono' Measure.restrict_le_self (le_refl _))

end SLEExactGauge

end

end OAI
