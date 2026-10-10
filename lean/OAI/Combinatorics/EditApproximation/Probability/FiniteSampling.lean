import OAI.Combinatorics.EditApproximation.Geometry.PublishedInputs

namespace OAI

/-!
# Finite uniform sampling

The shared group estimator samples child labels uniformly with replacement.
These lemmas use that finite distribution, including its product law;
they do not assume that different group representatives are independent.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def uniformMean {ι : Type*} [Fintype ι] (value : ι → ℝ) : ℝ :=
  (∑ i, value i) / Fintype.card ι

theorem uniform_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (value : ι → ℝ) :
    (∫ i, value i ∂(PMF.uniformOfFintype ι).toMeasure) = uniformMean value := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← mul_sum, uniformMean]
  ring

theorem uniformMean_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound) :
    0 ≤ uniformMean value ∧ uniformMean value ≤ bound := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (sum_nonneg fun i _ => (hvalue i).1) hc.le
  · apply (div_le_iff₀ hc).2
    have hsum := sum_le_sum (s := univ) fun i _ => (hvalue i).2
    simpa only [sum_const, card_univ, nsmul_eq_mul, mul_comm] using hsum

theorem uniform_centered_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound)
    (i : ι) : |value i - uniformMean value| ≤ bound := by
  have hm := uniformMean_bounds value hvalue
  exact abs_le.mpr ⟨by linarith [(hvalue i).1], by linarith [(hvalue i).2]⟩

theorem uniform_centered_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (value : ι → ℝ) :
    (∫ i, (value i - uniformMean value)
      ∂(PMF.uniformOfFintype ι).toMeasure) = 0 := by
  rw [integral_sub (.of_finite) (integrable_const _), uniform_integral, integral_const]
  simp

theorem uniform_variance_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound) :
    (∫ i, (value i - uniformMean value) ^ 2
      ∂(PMF.uniformOfFintype ι).toMeasure) ≤ bound * uniformMean value := by
  let μ := (PMF.uniformOfFintype ι).toMeasure
  have hmean : (∫ i, value i ∂μ) = uniformMean value := uniform_integral value
  have hexpand : (∫ i, (value i - uniformMean value) ^ 2 ∂μ) =
      (∫ i, value i ^ 2 ∂μ) - (uniformMean value) ^ 2 := by
    calc
      _ = ∫ i, (value i ^ 2 - 2 * uniformMean value * value i +
          (uniformMean value) ^ 2) ∂μ := by congr 1; funext i; ring
      _ = _ := by
        rw [integral_add (.of_finite) (integrable_const _),
          integral_sub (.of_finite) (.of_finite), integral_const_mul, hmean, integral_const]
        simp only [probReal_univ, one_smul]
        ring
  have hsecond : (∫ i, value i ^ 2 ∂μ) ≤ bound * uniformMean value := by
    rw [← hmean, ← integral_const_mul]
    apply integral_mono (.of_finite) (.of_finite)
    intro i
    nlinarith [(hvalue i).1, (hvalue i).2]
  rw [hexpand]
  nlinarith [sq_nonneg (uniformMean value)]

/-- Actual independent uniform draws, centered and divided by the sample
count. All measurability, centering and variance obligations for Bernstein
are derived from this product distribution. -/
theorem uniform_sample_average_concentration
    {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (n : ℕ) (hn : 0 < n) (value : ι → ℝ) (bound meanBound deviation : ℝ)
    (hbound : 0 < bound) (hmeanBound : 0 < meanBound) (hdev : 0 < deviation)
    (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound)
    (hmean : uniformMean value ≤ meanBound)
    (bernstein : FiniteBernsteinInput
      (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure)) :
    (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure).real
      {ω | deviation ≤ |(∑ j : Fin n, value (ω j)) / n - uniformMean value|} ≤
      2 * Real.exp (-(n : ℝ) * deviation ^ 2 /
        (2 * bound * meanBound + (2 / 3 : ℝ) * bound * deviation)) := by
  let μ := (PMF.uniformOfFintype ι).toMeasure
  let X : Fin n → (Fin n → ι) → ℝ :=
    fun j ω => (value (ω j) - uniformMean value) / n
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hindep : iIndepFun X (Measure.pi fun _ : Fin n => μ) := by
    exact iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ i => (value i - uniformMean value) / n)
      (fun _ => (measurable_of_finite _).aemeasurable)
  have hcenter : ∀ j, (∫ ω, X j ω ∂Measure.pi (fun _ : Fin n => μ)) = 0 := by
    intro j
    dsimp [X]
    rw [integral_comp_eval (μ := fun _ : Fin n => μ) (i := j)
      (f := fun i => (value i - uniformMean value) / n)
      (measurable_of_finite _).aestronglyMeasurable]
    rw [integral_div, uniform_centered_integral, zero_div]
  have hbounded : ∀ j, ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ),
      |X j ω| ≤ bound / n := by
    intro j
    filter_upwards [] with ω
    dsimp [X]
    rw [abs_div, abs_of_pos hnr]
    exact div_le_div_of_nonneg_right (uniform_centered_bound value hvalue _) hnr.le
  have hvariance : (∑ j : Fin n, ∫ ω, (X j ω) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ bound * meanBound / n := by
    have hpoint (j : Fin n) : (∫ ω, (X j ω) ^ 2
        ∂Measure.pi (fun _ : Fin n => μ)) ≤ bound * meanBound / n ^ 2 := by
      dsimp [X]
      rw [integral_comp_eval (μ := fun _ : Fin n => μ) (i := j)
        (f := fun i => ((value i - uniformMean value) / n) ^ 2)
        (measurable_of_finite _).aestronglyMeasurable]
      simp_rw [div_pow]
      rw [integral_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (uniform_variance_bound value hvalue).trans
        (mul_le_mul_of_nonneg_left hmean hbound.le)
    have hsum := sum_le_sum (s := univ) fun j _ => hpoint j
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    apply hsum.trans_eq
    field_simp
  have htail := bernstein n X (bound / n) (bound * meanBound / n) deviation
    (div_pos hbound hnr) (div_pos (mul_pos hbound hmeanBound) hnr) hdev hindep
    (fun _ => measurable_of_finite _) (fun _ => .of_finite) hcenter hbounded hvariance
  have hsum (ω : Fin n → ι) : (∑ j : Fin n, X j ω) =
      (∑ j : Fin n, value (ω j)) / n - uniformMean value := by
    dsimp [X]
    rw [← sum_div, sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hsum] at htail
  convert htail using 2
  congr 1
  field_simp

end EditApproximation

end OAI
