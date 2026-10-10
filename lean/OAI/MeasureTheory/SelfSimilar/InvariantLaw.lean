import OAI.MeasureTheory.SelfSimilar.Coding

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension.System
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι]

noncomputable def average (S : System ι) (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n+1 => fun x => ∑ i, S.weight i * average S f n (S.affine i x)

theorem average_continuous (S : System ι) {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    Continuous (S.average f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (ih.comp (S.affine_continuous i))

theorem average_bound (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (n : ℕ) (x : ℝ) : |S.average f n x| ≤ C := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    calc
      _ ≤ ∑ i, |S.weight i * S.average f n (S.affine i x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.weight i * C := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_nonneg (S.weight_nonneg i)]
        exact mul_le_mul_of_nonneg_left (ih _) (S.weight_nonneg i)
      _ = C := by rw [← Finset.sum_mul,S.weight_sum,one_mul]

theorem average_integrable (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) (μ : Measure ℝ)
    [IsFiniteMeasure μ] : Integrable (S.average f n) μ := by
  apply Integrable.of_bound (S.average_continuous hf n).aestronglyMeasurable C
  exact ae_of_all μ fun x => by simpa only [Real.norm_eq_abs] using S.average_bound hb n x

theorem selfSimilar_integral (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂μ) = ∑ i, S.weight i * ∫ x, f (S.affine i x) ∂μ := by
  have hi : ∀ i, Integrable f (μ.map (S.affine i)) := fun i =>
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure (fun i _ => (hi i).smul_measure (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_map (S.affine_continuous i).measurable.aemeasurable
    hf.aestronglyMeasurable,ENNReal.toReal_ofReal (S.weight_nonneg i)]
  rfl

theorem integral_average (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C)
    (n : ℕ) : (∫ x, S.average f n x ∂μ) = ∫ x, f x ∂μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫ x, ∑ i, S.weight i * S.average f n (S.affine i x) ∂μ) = _
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
      rw [← S.selfSimilar_integral μ hμ (S.average_continuous hf n) (S.average_bound hb n),ih]
    · intro i _
      apply Integrable.const_mul
      apply Integrable.of_bound ((S.average_continuous hf n).comp
        (S.affine_continuous i)).aestronglyMeasurable C
      exact ae_of_all μ fun x => by
        simpa only [Real.norm_eq_abs,Function.comp_def] using S.average_bound hb n (S.affine i x)

theorem average_difference (S : System ι) {f : ℝ → ℝ} {c ε δ : ℝ}
    (hc : 0 ≤ c) (hr : ∀ i, |S.ratio i| ≤ c)
    (hf : ∀ x y, |x-y| < δ → |f x-f y| ≤ ε) (n : ℕ) {x y : ℝ}
    (hxy : |x-y| *c^n < δ) : |S.average f n x-S.average f n y| ≤ ε := by
  induction n generalizing x y with
  | zero => simpa only [average,pow_zero,mul_one] using hf x y (by simpa using hxy)
  | succ n ih =>
    simp only [average,← Finset.sum_sub_distrib,← mul_sub]
    calc
      _ ≤ ∑ i, |S.weight i * (S.average f n (S.affine i x)-S.average f n (S.affine i y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.weight i * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_nonneg (S.weight_nonneg i)]
        apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
        apply ih
        have he : S.affine i x-S.affine i y = S.ratio i*(x-y) := by simp only [affine]; ring
        rw [he,abs_mul]
        calc
          _ ≤ (c*|x-y|)*c^n := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hr i) (abs_nonneg _)) (pow_nonneg hc n)
          _ = |x-y| *c^(n+1) := by rw [pow_succ]; ring
          _ < δ := hxy
      _ = ε := by rw [← Finset.sum_mul,S.weight_sum,one_mul]

variable [Nonempty ι]

theorem tendsto_average_at_zero (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ}
    (hf : UniformContinuous f) (hb : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => S.average f n 0) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  obtain ⟨B,hB,hBc⟩ := S.selfSimilar_compact μ hμ
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by linarith)
  have hlim : Tendsto (fun n : ℕ => B*c^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).const_mul B
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 δ hδ)
  refine ⟨N,fun n hn => ?_⟩
  have hai := S.average_integrable hf.continuous hb n μ
  have he : (∫ x, (S.average f n x-S.average f n 0) ∂μ) =
      (∫ x, f x ∂μ) - S.average f n 0 := by
    rw [integral_sub hai (integrable_const _),S.integral_average μ hμ hf.continuous hb]
    simp
  have hbound : ∀ᵐ x ∂μ, ‖S.average f n x-S.average f n 0‖ ≤ ε/2 := by
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ Icc (-B) B from ae_iff.mpr hBc] with x hx
    rw [Real.norm_eq_abs]
    apply S.average_difference hc.le hr (fun x y h => (hd (by simpa [Real.dist_eq] using h)).le)
    calc
      |x-0| *c^n ≤ B*c^n := mul_le_mul_of_nonneg_right (by simpa using abs_le.mpr hx)
        (pow_nonneg hc.le n)
      _ < δ := hN n hn
  have hnorm := norm_integral_le_of_norm_le_const hbound
  rw [he] at hnorm
  have hh : |(∫ x, f x ∂μ)-S.average f n 0| ≤ ε/2 := by simpa using hnorm
  rw [Real.dist_eq,abs_sub_comm]
  linarith

theorem selfSimilar_unique (S : System ι) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : S.SelfSimilar μ) (hν : S.SelfSimilar ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  have hb : ∀ x, |f x| ≤ ‖f.toBoundedContinuousFunction‖ := fun x => by
    have hh := f.toBoundedContinuousFunction.norm_coe_le_norm x
    have he : f.toBoundedContinuousFunction x = f x := rfl
    rw [he,Real.norm_eq_abs] at hh
    exact hh
  exact tendsto_nhds_unique (S.tendsto_average_at_zero μ hμ hf hb)
    (S.tendsto_average_at_zero ν hν hf hb)

end EntropyRateDimension.System

end

end OAI
