import Mathlib
import OAI.Analysis.Commutator.DecomposableAlgebra

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma add_field_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ}
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    ∀ᵐ a ∂μ,‖T a+S a‖≤b+c := by
  filter_upwards [hb,hc] with a ha hc
  exact (norm_add_le _ _).trans (add_le_add ha hc)

omit [CompleteSpace H] in
lemma operator_add (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    operator μ (fun a => T a+S a) (add_measurable μ T S hT hS)
      (add_field_bound μ T S hb hc)=operator μ T hT hb+operator μ S hS hc := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_ae μ (fun a => T a+S a) (add_measurable μ T S hT hS)
    (add_field_bound μ T S hb hc) f,operator_ae μ T hT hb f,operator_ae μ S hS hc f,
    Lp.coeFn_add (operator μ T hT hb f) (operator μ S hS hc f)] with a h1 h2 h3 h4
  change operator μ (fun a => T a+S a) (add_measurable μ T S hT hS)
    (add_field_bound μ T S hb hc) f a=(operator μ T hT hb f+operator μ S hS hc f) a
  rw [h1,h4]
  change T a (f a)+S a (f a)=operator μ T hT hb f a+operator μ S hS hc f a
  rw [h2,h3]

end Kadison.Decomposable

end

end
end

end OAI
