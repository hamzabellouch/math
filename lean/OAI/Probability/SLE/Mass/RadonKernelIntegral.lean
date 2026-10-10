import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Signed integrals of a random Radon measure can be computed from its
mean measure. The positive and negative parts use Tonelli separately. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

lemma lintegral_ofReal_lt_top_of_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ⊤ := by
  apply (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (le_abs_self (f x)))).trans_lt
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => norm_nonneg (f x)))).mp
    hf.norm.hasFiniteIntegral

theorem integrable_integral_bind_of_sections
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (hμ : Measurable μ)
    (f : X → ℝ) (hf : Measurable f)
    (hfi : ∀ ω, Integrable f (μ ω)) (hfP : Integrable f (P.bind μ)) :
    Integrable (fun ω => ∫ x, f x ∂μ ω) P ∧
      (∫ ω, (∫ x, f x ∂μ ω) ∂P) = ∫ x, f x ∂P.bind μ := by
  let A (ω : Ω) := ∫⁻ x, ENNReal.ofReal (f x) ∂μ ω
  let B (ω : Ω) := ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ω
  have hAm : Measurable A := (Measure.measurable_lintegral hf.ennreal_ofReal).comp hμ
  have hBm : Measurable B := (Measure.measurable_lintegral hf.neg.ennreal_ofReal).comp hμ
  have hA : (∫⁻ ω, A ω ∂P) = ∫⁻ x, ENNReal.ofReal (f x) ∂P.bind μ :=
    (Measure.lintegral_bind hμ.aemeasurable hf.ennreal_ofReal.aemeasurable).symm
  have hB : (∫⁻ ω, B ω ∂P) = ∫⁻ x, ENNReal.ofReal (-f x) ∂P.bind μ :=
    (Measure.lintegral_bind hμ.aemeasurable hf.neg.ennreal_ofReal.aemeasurable).symm
  have hAf : (∫⁻ ω, A ω ∂P) < ⊤ := hA.trans_lt (lintegral_ofReal_lt_top_of_integrable hfP)
  have hBf : (∫⁻ ω, B ω ∂P) < ⊤ := hB.trans_lt (lintegral_ofReal_lt_top_of_integrable hfP.neg)
  have he (ω : Ω) : (∫ x, f x ∂μ ω) = (A ω).toReal - (B ω).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfi ω)
  refine ⟨?_,?_⟩
  · convert (integrable_toReal_of_lintegral_ne_top hAm.aemeasurable hAf.ne).sub
      (integrable_toReal_of_lintegral_ne_top hBm.aemeasurable hBf.ne) using 1
    funext ω
    exact he ω
  simp_rw [he]
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hAm.aemeasurable hAf.ne)
    (integrable_toReal_of_lintegral_ne_top hBm.aemeasurable hBf.ne),
    integral_toReal hAm.aemeasurable (Eventually.of_forall (fun ω =>
      lintegral_ofReal_lt_top_of_integrable (hfi ω))),
    integral_toReal hBm.aemeasurable (Eventually.of_forall (fun ω =>
      lintegral_ofReal_lt_top_of_integrable (hfi ω).neg)),hA,hB]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfP).symm

theorem integral_bind_of_integrable_sections
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (hμ : Measurable μ)
    (f : X → ℝ) (hf : Measurable f)
    (hfi : ∀ ω, Integrable f (μ ω)) (hfP : Integrable f (P.bind μ)) :
    (∫ ω, (∫ x, f x ∂μ ω) ∂P) = ∫ x, f x ∂P.bind μ :=
  (integrable_integral_bind_of_sections P μ hμ f hf hfi hfP).2

end SLEExactGauge

end

end OAI
