import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
namespace BoundedAverageConcentration

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measureReal_average_ge_le
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
    μ.real {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      Real.exp (-(s.card : ℝ) * τ ^ 2 / 2) := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hcenter : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ := by
    exact h_indep.comp (fun i x => x - ∫ ω, X i ω ∂μ)
      (fun _ => measurable_id.sub_const _)
  have hsub : ∀ i ∈ s,
      HasSubgaussianMGF (fun ω => X i ω - ∫ x, X i x ∂μ) (1 / 4 : ℝ≥0) μ := by
    intro i hi
    convert hasSubgaussianMGF_of_mem_Icc (h_meas i hi) (h_bdd i hi) using 1
    norm_num
  have hsum_mean : (∑ i ∈ s, ∫ x, X i x ∂μ) ≤ (s.card : ℝ) * τ / 2 := by
    calc
      (∑ i ∈ s, ∫ x, X i x ∂μ) ≤ ∑ _i ∈ s, τ / 2 :=
        Finset.sum_le_sum h_mean
      _ = (s.card : ℝ) * τ / 2 := by simp [mul_div_assoc]
  have hsubset : {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ⊆
      {ω | (s.card : ℝ) * τ / 2 ≤ ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)} := by
    intro ω hω
    have hw : τ * (s.card : ℝ) ≤ ∑ i ∈ s, X i ω :=
      (le_div_iff₀ hcard).mp hω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib]
    nlinarith
  have hhoeff := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcenter hsub
    (show 0 ≤ (s.card : ℝ) * τ / 2 by positivity)
  have hexp :
      -((s.card : ℝ) * τ / 2) ^ 2 /
          (2 * ((∑ _i ∈ s, (1 / 4 : ℝ≥0) : ℝ≥0) : ℝ)) =
        -(s.card : ℝ) * τ ^ 2 / 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    push_cast
    field_simp [ne_of_gt hcard]
    ring
  exact (measureReal_mono hsubset).trans (hexp ▸ hhoeff)

theorem measure_average_ge_le
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
    μ {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(s.card : ℝ) * τ ^ 2 / 2)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (measureReal_average_ge_le h_indep s hs hτ h_meas h_bdd h_mean)

theorem exponential_card_bound
    {N b ℓ q : ℝ} (hb : 0 < b) (hℓ : 0 ≤ ℓ)
    (hq : q ≤ Real.log b / 8)
    (hN : b ^ (ℓ / 2 - 1) ≤ N) :
    Real.exp (-N * (Real.exp (-q * ℓ)) ^ 2 / 2) ≤
      Real.exp (-(b ^ (ℓ / 4)) / (2 * b)) := by
  have hpow : 0 < b ^ (ℓ / 2 - 1) := Real.rpow_pos_of_pos hb _
  have hexp : Real.exp (-(Real.log b) * ℓ / 4) ≤ (Real.exp (-q * ℓ)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hq hℓ]
  have hprod : b ^ (ℓ / 4) / b ≤ N * (Real.exp (-q * ℓ)) ^ 2 := by
    calc
      b ^ (ℓ / 4) / b =
          b ^ (ℓ / 2 - 1) * Real.exp (-(Real.log b) * ℓ / 4) := by
        rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb,
          ← Real.exp_log hb, ← Real.exp_sub, ← Real.exp_add]
        simp only [Real.log_exp]
        congr 1
        ring
      _ ≤ N * (Real.exp (-q * ℓ)) ^ 2 :=
        mul_le_mul hN hexp (Real.exp_pos _).le (hpow.le.trans hN)
  apply Real.exp_le_exp.mpr
  have := div_le_div_of_nonneg_right hprod (show (0 : ℝ) ≤ 2 by norm_num)
  simpa [div_div, neg_div, mul_comm] using neg_le_neg this

theorem measureReal_average_ge_le_double_exp
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {b ℓ q : ℝ}
    (hb : 0 < b) (hℓ : 0 ≤ ℓ) (hq : q ≤ Real.log b / 8)
    (hcard : b ^ (ℓ / 2 - 1) ≤ (s.card : ℝ))
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ Real.exp (-q * ℓ) / 2) :
    μ.real {ω | Real.exp (-q * ℓ) ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      Real.exp (-(b ^ (ℓ / 4)) / (2 * b)) := by
  exact (measureReal_average_ge_le h_indep s hs (Real.exp_pos _).le
    h_meas h_bdd h_mean).trans (exponential_card_bound hb hℓ hq hcard)

theorem measure_average_ge_le_of_kernel
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y Ω) [IsMarkovKernel κ]
    {X : ι → Ω → ℝ} (s : Finset ι) (hs : s.Nonempty)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h_meas : ∀ i ∈ s, Measurable (X i))
    (h_indep : ∀ᵐ y ∂ν, iIndepFun X (κ y))
    (h_bdd : ∀ᵐ y ∂ν, ∀ i ∈ s, ∀ᵐ ω ∂κ y, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ᵐ y ∂ν, ∀ i ∈ s, (∫ ω, X i ω ∂κ y) ≤ τ / 2) :
    (κ ∘ₘ ν) {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(s.card : ℝ) * τ ^ 2 / 2)) := by
  have hsum : Measurable (fun ω => ∑ i ∈ s, X i ω) :=
    Finset.measurable_fun_sum s h_meas
  rw [Measure.bind_apply (measurableSet_le measurable_const (hsum.div_const _))
    κ.aemeasurable]
  calc
    (∫⁻ y, κ y {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ∂ν) ≤
        ∫⁻ _y, ENNReal.ofReal (Real.exp (-(s.card : ℝ) * τ ^ 2 / 2)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [h_indep, h_bdd, h_mean] with y hy_indep hy_bdd hy_mean
      exact measure_average_ge_le hy_indep s hs hτ
        (fun i hi => (h_meas i hi).aemeasurable) hy_bdd hy_mean
    _ = ENNReal.ofReal (Real.exp (-(s.card : ℝ) * τ ^ 2 / 2)) := by simp

theorem attenuation_le_half_threshold
    {c η x : ℝ} (hx : 0 ≤ x) (hη : η ≤ c / 4)
    (hlength : 4 * Real.log 2 ≤ c * x) :
    Real.exp (-c * x / 2) ≤ Real.exp (-η * x) / 2 := by
  apply (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
  conv_lhs => rhs; rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hη hx]

end BoundedAverageConcentration
end Problem367

end

end OAI
