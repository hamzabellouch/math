import Mathlib
import OAI.Analysis.Commutator.DecomposableOperator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma operator_eq_of_ae_apply (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (A : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hA : ∀ f : Lp H 2 μ,A f =ᵐ[μ] fun a => T a (f a)) :
    A=operator μ T hm hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (hA f).trans (operator_ae μ T hm hb f).symm

lemma add_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a+S a) ξ) μ := (hT ξ).add (hS ξ)

lemma sub_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a-S a) ξ) μ := (hT ξ).sub (hS ξ)

lemma mul_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a*S a) ξ) μ := measurable_apply μ T hT (hS ξ)

lemma sub_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ}
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    ∀ᵐ a ∂μ,‖T a-S a‖≤b+c := by
  filter_upwards [hb,hc] with a ha hb
  exact (norm_sub_le _ _).trans (add_le_add ha hb)

lemma mul_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ} (hb0 : 0≤b)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    ∀ᵐ a ∂μ,‖T a*S a‖≤b*c := by
  filter_upwards [hb,hc] with a ha hc
  exact (norm_mul_le _ _).trans (mul_le_mul ha hc (norm_nonneg _) hb0)

lemma operator_sub (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    operator μ T hT hb-operator μ S hS hc=
      operator μ (fun a => T a-S a) (sub_measurable μ T S hT hS) (sub_bound μ T S hb hc) := by
  apply operator_eq_of_ae_apply
  intro f
  filter_upwards [operator_ae μ T hT hb f,operator_ae μ S hS hc f,
    Lp.coeFn_sub (operator μ T hT hb f) (operator μ S hS hc f)] with a h1 h2 h3
  change (operator μ T hT hb f-operator μ S hS hc f) a=_
  rw [h3]
  exact congrArg₂ (·-·) h1 h2

lemma operator_mul (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb0 : 0≤b) (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    operator μ T hT hb*operator μ S hS hc=
      operator μ (fun a => T a*S a) (mul_measurable μ T S hT hS) (mul_bound μ T S hb0 hb hc) := by
  apply operator_eq_of_ae_apply
  intro f
  filter_upwards [operator_ae μ T hT hb (operator μ S hS hc f),operator_ae μ S hS hc f]
    with a ha hs
  change (operator μ T hT hb (operator μ S hS hc f)) a=_
  rw [ha,hs]
  rfl

end Kadison.Decomposable

end

end
end

end OAI
