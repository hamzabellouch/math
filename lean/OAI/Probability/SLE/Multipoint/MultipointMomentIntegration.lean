import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-! Finite products and Tonelli for the moments of a nonnegative spatial
weight. These identities retain arbitrary finite orders. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

lemma lintegral_fin_product
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ x : Fin n → X, ∏ i, f (x i) ∂Measure.pi (fun _ => μ)) = (∫⁻ x, f x ∂μ)^n := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty,Finset.prod_empty,lintegral_const,
      one_mul,pow_zero,Measure.pi_empty_univ]
  | succ n ih =>
    rw [← (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (fun x : Fin (n+1) → X => ∏ i, f (x i))]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Fin.prod_univ_succ,Fin.insertNth_zero,Fin.zero_succAbove,Equiv.coe_fn_mk,
      Fin.cons_succ,cast_eq,Fin.cons_zero]
    have hg : Measurable (fun x : Fin n → X => ∏ i, f (x i)) :=
      Finset.measurable_prod Finset.univ (fun i _ => hf.comp (measurable_pi_apply i))
    rw [lintegral_prod_mul (f := f) (g := fun x : Fin n → X => ∏ i, f (x i))
      hf.aemeasurable hg.aemeasurable,ih,pow_succ,mul_comm]

theorem lintegral_mass_pow_eq
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) [SigmaFinite P] [SigmaFinite μ]
    (W : Ω → X → ℝ≥0∞) (hW : Measurable (Function.uncurry W)) (n : ℕ) :
    (∫⁻ ω, (∫⁻ x, W ω x ∂μ)^n ∂P) =
      ∫⁻ x : Fin n → X, ∫⁻ ω, ∏ i, W ω (x i) ∂P ∂Measure.pi (fun _ => μ) := by
  have he (ω : Ω) := lintegral_fin_product μ (W ω)
    (hW.comp (measurable_const.prodMk measurable_id)) n
  simp_rw [← he]
  apply lintegral_lintegral_swap
  apply Measurable.aemeasurable
  apply Finset.measurable_prod
  intro i _
  exact hW.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem lintegral_mass_pow_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) [SigmaFinite P] [SigmaFinite μ]
    (W : Ω → X → ℝ≥0∞) (hW : Measurable (Function.uncurry W)) (n : ℕ)
    (K : (Fin n → X) → ℝ≥0∞)
    (hK : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), (∫⁻ ω, ∏ i, W ω (x i) ∂P) ≤ K x) :
    (∫⁻ ω, (∫⁻ x, W ω x ∂μ)^n ∂P) ≤ ∫⁻ x, K x ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [lintegral_mass_pow_eq P μ W hW n]
  exact lintegral_mono_ae hK

end SLEExactGauge.Multipoint

end

end OAI
