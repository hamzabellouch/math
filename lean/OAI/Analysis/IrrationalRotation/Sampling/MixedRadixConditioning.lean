import OAI.Analysis.IrrationalRotation.Couplings.ConditionalObservationTransport
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixHaarLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory

namespace Invariant233.MixedRadix

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {r : ℕ → ℕ}

theorem ae_circleCanonical_circleValue_of_map_ac
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {D : Ω → Digits r} (hD : Measurable D)
    (hAC : μ.map D ≪ digitLaw r hp) :
    ∀ᵐ ω ∂μ, circleCanonical r hp (circleValue (D ω)) = D ω := by
  exact ae_of_ae_map hD.aemeasurable
    (hAC.ae_le (ae_circleCanonical_circleValue hr hp))

variable [IsFiniteMeasure μ]

theorem condExp_circleValue_eq_digits
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {D : Ω → Digits r} (hD : Measurable D)
    (hAC : μ.map D ≪ digitLaw r hp) (f : Ω → E) :
    μ[f | MeasurableSpace.comap (circleValue ∘ D) inferInstance] =ᵐ[μ]
      μ[f | MeasurableSpace.comap D inferInstance] :=
  ConditionalObservationTransport.condExp_encoding hD (measurable_circleValue hr)
    (measurable_circleCanonical r hp)
    (ae_circleCanonical_circleValue_of_map_ac hr hp hD hAC) f

theorem condExp_circleValue_coordinate_formula
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {D : Ω → Digits r} (hD : Measurable D)
    (hAC : μ.map D ≪ digitLaw r hp) (i : ℕ)
    (f : Ω → ℝ) (posterior : Fin (r i) → ℝ)
    (hposterior : μ[f | MeasurableSpace.comap D inferInstance] =ᵐ[μ]
      fun ω => posterior (D ω i)) :
    μ[f | MeasurableSpace.comap (circleValue ∘ D) inferInstance] =ᵐ[μ]
      fun ω => posterior (circleCanonical r hp (circleValue (D ω)) i) :=
  ConditionalObservationTransport.condExp_encoding_formula hD (measurable_circleValue hr)
    (measurable_circleCanonical r hp)
    (ae_circleCanonical_circleValue_of_map_ac hr hp hD hAC) f
    (fun d => posterior (d i)) hposterior

theorem iCondIndepFun_circleValue_iff_digits
    [StandardBorelSpace Ω] {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {D : Ω → Digits r} (hD : Measurable D)
    (hAC : μ.map D ≪ digitLaw r hp)
    (L : ∀ i, Ω → β i) (hL : ∀ i, Measurable (L i)) :
    iCondIndepFun (MeasurableSpace.comap (circleValue ∘ D) inferInstance)
      ((measurable_circleValue hr).comp hD).comap_le L μ ↔
    iCondIndepFun (MeasurableSpace.comap D inferInstance) hD.comap_le L μ :=
  ConditionalObservationTransport.iCondIndepFun_encoding_iff hD (measurable_circleValue hr)
    (measurable_circleCanonical r hp)
    (ae_circleCanonical_circleValue_of_map_ac hr hp hD hAC) L hL

end Invariant233.MixedRadix

end

end OAI
