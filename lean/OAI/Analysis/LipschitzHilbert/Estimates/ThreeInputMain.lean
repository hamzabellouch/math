import OAI.Analysis.LipschitzHilbert.ConditionalMain
import OAI.Analysis.LipschitzHilbert.Fourier.BandToFullProof

namespace OAI

/-! The manuscript's main conclusions with the band-to-full input proved.
Only the three explicitly cited classical inputs remain as hypotheses. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem main_of_three_published_inputs (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C :=
  conditional_main hVariation hLL hH bandToFullInput_proved

theorem uniform_truncation_of_three_published_inputs
    (hVariation : LepingleInput) (hLL : LaceyLiInput) (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
  conditional_uniform_truncation hVariation hLL hH bandToFullInput_proved

end LipschitzHilbert

end

end OAI
