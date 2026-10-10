import OAI.Analysis.IrrationalRotation.Model.CircleConditionalLabels
import OAI.Analysis.IrrationalRotation.Couplings.CircleConditionalProbabilities

namespace OAI

noncomputable section
namespace Invariant233.CircleCoupling

theorem conditionalLabelLaws {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : ConditionalLabelLaws p j hr where
  probability := law_isProbabilityMeasure hp j
  endpoint_measurable := measurable_point hp hr
  independent := iCondIndepFun_labels_point hp j hr
  finite_posterior := condExp_labels_point hp j hr
  top_probability := fun _ hs _ hi which => ae_top_conditional_probability hp j hr hs hi which
  bottom_probability := fun _ hs _ hi which => ae_bottom_conditional_probability hp j hr hs hi which
  top_forcing := fun _ hs _ hi which => ae_top_forces hp j hr hs hi which
  bottom_forcing := fun _ hs _ hi which => ae_bottom_forces hp j hr hs hi which

theorem exists_conditionalLabelLaws {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i, ConditionalLabelLaws p j hr :=
  ⟨MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible,
    conditionalLabelLaws hp j _⟩

end Invariant233.CircleCoupling

end

end OAI
