import OAI.Probability.IsingPerceptron.MomentLogLimit

namespace OAI

/-! Polynomial approximation of reciprocal normalizers in bounded
replica tests. Extra-replica mixed moments determine the limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Polynomial

namespace InvariantIsing

lemma cavity_weighted_comp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Integrable (fun ω => A ω * f (Z ω)) P := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hzs : Measurable (fun ω => (⟨Z ω, hZb ω⟩ : Icc a b)) := hZ.subtype_mk
  have hm : Measurable (fun ω => f (Z ω)) := hf.domRestrict.measurable.comp hzs
  apply Integrable.of_bound (hA.mul hm).aestronglyMeasurable (B * C)
  exact ae_of_all _ fun ω => by
    change ‖A ω * f (Z ω)‖ ≤ B * C
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hAb ω) (hC _ (hZb ω)) (norm_nonneg _) ((abs_nonneg _).trans (hAb ω))

lemma cavity_weighted_polynomial_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B) (p : ℝ[X]) :
    (∫ ω, A ω * p.eval (Z ω) ∂P) =
      ∑ k ∈ p.support, p.coeff k * ∫ ω, A ω * Z ω ^ k ∂P := by
  have he (ω : Ω) : A ω * p.eval (Z ω) =
      ∑ k ∈ p.support, p.coeff k * (A ω * Z ω ^ k) := by
    simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ =>
    (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb
      (fun x => x ^ k) (continuous_pow k).continuousOn).const_mul (p.coeff k))]
  simp only [integral_const_mul]

lemma cavity_weighted_approx_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B η : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    |(∫ ω, A ω * f (Z ω) ∂P) - ∫ ω, A ω * g (Z ω) ∂P| ≤ B * η := by
  rw [← integral_sub (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb f hf)
    (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb g hg), ← Real.norm_eq_abs]
  have ht := norm_integral_le_of_norm_le_const (μ := P) (C := B * η)
    (f := fun ω => A ω * f (Z ω) - A ω * g (Z ω)) (ae_of_all _ fun ω => by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hAb ω) (hfg _ (hZb ω)) (abs_nonneg _) ((abs_nonneg _).trans (hAb ω)))
  simpa only [probReal_univ, mul_one] using ht

theorem cavity_weighted_moments_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : Ω₀ → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : Measurable W) (hD : Measurable D) {a b B : ℝ} (hB : 0 ≤ B)
    (hZb : ∀ n ω, Z n ω ∈ Icc a b) (hWb : ∀ ω, W ω ∈ Icc a b)
    (hAb : ∀ n ω, |A n ω| ≤ B) (hDb : ∀ ω, |D ω| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ ω, A n ω * Z n ω ^ k ∂P n) atTop
      (𝓝 (∫ ω, D ω * W ω ^ k ∂Q)))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => ∫ ω, A n ω * f (Z n ω) ∂P n) atTop
      (𝓝 (∫ ω, D ω * f (W ω) ∂Q)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (3 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηb : B * η < ε / 3 := by
    have he : 3 * (B + 1) * η = ε := mul_div_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf η hη
  have ht : Tendsto (fun n => ∫ ω, A n ω * p.eval (Z n ω) ∂P n) atTop
      (𝓝 (∫ ω, D ω * p.eval (W ω) ∂Q)) := by
    simp_rw [cavity_weighted_polynomial_integral (P _) (Z _) (A _) (hZ _) (hA _) (hZb _) (hAb _) p,
      cavity_weighted_polynomial_integral Q W D hW hD hWb hDb p]
    exact tendsto_finsetSum _ fun k _ => tendsto_const_nhds.mul (hmom k)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have h1 := cavity_weighted_approx_error (P n) (Z n) (A n) (hZ n) (hA n)
    (hZb n) (hAb n) (fun x => p.eval x) f p.continuous.continuousOn hf
    (fun x hx => (hp x hx).le)
  have h2 := cavity_weighted_approx_error Q W D hW hD hWb hDb
    (fun x => p.eval x) f p.continuous.continuousOn hf (fun x hx => (hp x hx).le)
  have h3 := hN n hn
  rw [Real.dist_eq] at h3
  calc
    _ ≤ |(∫ ω, A n ω * f (Z n ω) ∂P n) - ∫ ω, D ω * p.eval (W ω) ∂Q| +
        |(∫ ω, D ω * p.eval (W ω) ∂Q) - ∫ ω, D ω * f (W ω) ∂Q| := abs_sub_le _ _ _
    _ ≤ |(∫ ω, A n ω * f (Z n ω) ∂P n) - ∫ ω, A n ω * p.eval (Z n ω) ∂P n| +
        |(∫ ω, A n ω * p.eval (Z n ω) ∂P n) - ∫ ω, D ω * p.eval (W ω) ∂Q| +
        |(∫ ω, D ω * p.eval (W ω) ∂Q) - ∫ ω, D ω * f (W ω) ∂Q| :=
      add_le_add (abs_sub_le _ _ _) le_rfl
    _ < ε := by rw [abs_sub_comm] at h1; linarith

theorem cavity_reciprocal_normalizer_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : Ω₀ → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : Measurable W) (hD : Measurable D) {a b B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B)
    (hZb : ∀ n ω, Z n ω ∈ Icc a b) (hWb : ∀ ω, W ω ∈ Icc a b)
    (hAb : ∀ n ω, |A n ω| ≤ B) (hDb : ∀ ω, |D ω| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ ω, A n ω * Z n ω ^ k ∂P n) atTop
      (𝓝 (∫ ω, D ω * W ω ^ k ∂Q))) (r : ℕ) :
    Tendsto (fun n => ∫ ω, A n ω / Z n ω ^ r ∂P n) atTop
      (𝓝 (∫ ω, D ω / W ω ^ r ∂Q)) := by
  have hc : ContinuousOn (fun z : ℝ => 1 / z ^ r) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow r)
      (fun z hz => pow_ne_zero _ (ha.trans_le hz.1).ne')
  simpa only [one_div, ← div_eq_mul_inv] using
    cavity_weighted_moments_tendsto P Q Z A W D hZ hA hW hD hB hZb hWb hAb hDb hmom
      (fun z => 1 / z ^ r) hc

end InvariantIsing

end

end OAI
