import OAI.Probability.LatticePassage.FiniteVariance

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

lemma variance_le_integral_square_sub {f : α → ℝ} (hf : Measurable f) (c : ℝ) :
    variance f μ ≤ ∫ u, (f u-c)^2 ∂μ := by
  have h := variance_le_expectation_sq (μ := μ) (hf.sub_const c).aestronglyMeasurable
  rw [variance_sub_const hf.aestronglyMeasurable c] at h
  exact h

theorem bounded_efron_stein {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫ z : (ι → α) × (ι → α),
        (f (Function.update z.1 i (z.2 i)) - f z.1)^2
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  apply (variance_pi_le_sum_coordinateVariance μ hf hC0 hC).trans
  apply sum_le_sum
  intro i _
  let G := fun z : (ι → α) × (ι → α) => (f (Function.update z.1 i (z.2 i))-f z.1)^2
  have hGm : Measurable G := by dsimp [G]; fun_prop
  have hGb : ∀ z, |G z| ≤ (2*C)^2 := by
    intro z
    have hb : |f (Function.update z.1 i (z.2 i))-f z.1| ≤ 2*C :=
      (abs_sub _ _).trans (by linarith [hC (Function.update z.1 i (z.2 i)), hC z.1])
    dsimp [G]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp hb]
  have hGi := (bounded_memLp_two (μ := (Measure.pi (fun _ : ι => μ)).prod
      (Measure.pi (fun _ : ι => μ))) hGm ((2*C)^2) hGb).integrable (by norm_num)
  rw [integral_prod _ hGi]
  apply integral_mono (integrable_coordinateVariance μ hf hC0 hC i) hGi.integral_prod_left
  intro v
  have he : (∫ w : ι → α, G (v,w) ∂Measure.pi (fun _ : ι => μ)) =
      ∫ u, (f (Function.update v i u)-f v)^2 ∂μ := by
    exact integral_comp_eval (μ := fun _ : ι => μ) (i := i)
      (f := fun u => (f (Function.update v i u)-f v)^2)
      (show Measurable (fun u => (f (Function.update v i u)-f v)^2) from by fun_prop).aestronglyMeasurable
  change coordinateVariance μ f i v ≤ ∫ w, G (v,w) ∂Measure.pi (fun _ : ι => μ)
  rw [he]
  exact variance_le_integral_square_sub μ (hf.comp (by fun_prop)) (f v)

theorem bounded_centered_square_lintegral {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    (∫⁻ v : ι → α, ENNReal.ofReal ((f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2)
      ∂Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
        ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2)
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  have hv := ENNReal.ofReal_le_ofReal (bounded_efron_stein μ hf hC0 hC)
  rw [variance_eq_integral hf.aemeasurable] at hv
  have hm := bounded_memLp_two (μ := Measure.pi (fun _ : ι => μ)) hf C hC
  rw [ofReal_integral_eq_lintegral_ofReal (f := fun v => (f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2) (hm.sub (memLp_const _)).integrable_sq
    (by filter_upwards [] with v; positivity)] at hv
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (fun z => sq_nonneg _))] at hv
  apply hv.trans
  apply sum_le_sum
  intro i _
  have hm : MemLp (fun z : (ι → α) × (ι → α) =>
      f (Function.update z.1 i (z.2 i))-f z.1) 2
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
    apply bounded_memLp_two (by fun_prop) (2*C)
    intro z
    exact (abs_sub _ _).trans (by linarith [hC (Function.update z.1 i (z.2 i)), hC z.1])
  rw [ofReal_integral_eq_lintegral_ofReal hm.integrable_sq
    (by filter_upwards [] with z; positivity)]

end CompanionFPP

end OAI
