import OAI.Analysis.LipschitzHilbert.Estimates.ThreeInputMain
import OAI.Analysis.LipschitzHilbert.Estimates.HorizontalHilbertProof

namespace OAI

/-! Uniform short directional Hilbert transform estimates conditional on
Lacey–Li and martingale variation bounds, using frequency reassembly and
classical one-dimensional Hilbert estimates. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem main_of_two_published_inputs (hVariation : LepingleInput) (hLL : LaceyLiInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C :=
  main_of_three_published_inputs hVariation hLL horizontalHilbertInput_proved

theorem uniform_truncation_of_two_published_inputs
    (hVariation : LepingleInput) (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
  uniform_truncation_of_three_published_inputs hVariation hLL horizontalHilbertInput_proved

end LipschitzHilbert

end

end OAI
