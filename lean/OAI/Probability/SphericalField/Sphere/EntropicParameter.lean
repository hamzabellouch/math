import Mathlib

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SphericalPerceptron

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma mem_interior_integrableExpSet_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    t ∈ interior (integrableExpSet X μ) := by
  have he : integrableExpSet X μ=univ := Set.eq_univ_of_forall hX
  simp [he]

omit [IsProbabilityMeasure μ] in
lemma cgf_analytic_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    AnalyticAt ℝ (cgf X μ) t :=
  analyticAt_cgf (mem_interior_integrableExpSet_of_all μ hX t)

lemma cgf_second_nonneg
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    0 ≤ deriv (deriv (cgf X μ)) t := by
  have hh := iteratedDeriv_two_cgf_eq_integral
    (mem_interior_integrableExpSet_of_all μ hX t)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hh
  rw [hh]
  exact div_nonneg (integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (mgf_pos (hX t)).le

lemma cgf_deriv_monotone
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    Monotone (deriv (cgf X μ)) :=
  monotone_of_deriv_nonneg (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt)
    (cgf_second_nonneg μ hX)

def entropicMean (p : ℝ) (X : Ω → ℝ) : ℝ :=
  ∫ t : ℝ in (0:ℝ)..1, deriv (cgf X μ) (p*t)

lemma entropicMean_eq_div (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {p : ℝ} (hp : p ≠ 0) : entropicMean μ p X=cgf X μ p/p := by
  rw [entropicMean,intervalIntegral.integral_comp_mul_left _ hp]
  simp only [mul_zero,mul_one]
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (cgf_analytic_of_all μ hX t).differentiableAt.hasDerivAt)
    (hc.intervalIntegrable _ _),cgf_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma entropicMean_zero (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    entropicMean μ 0 X=∫ ω, X ω ∂μ := by
  simp [entropicMean,deriv_cgf_zero (mem_interior_integrableExpSet_of_all μ hX 0)]

lemma entropicMean_monotone (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    Monotone (fun p => entropicMean μ p X) := by
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  intro p q hpq
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => p*t))).intervalIntegrable 0 1)
    ((hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => q*t))).intervalIntegrable 0 1)
  intro t ht
  exact cgf_deriv_monotone μ hX (mul_le_mul_of_nonneg_right hpq ht.1)

lemma entropicMean_param_bound
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, deriv (deriv (cgf X μ)) t ≤ K)
    {p q : ℝ} (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |entropicMean μ p X-entropicMean μ q X| ≤ K*|p-q| := by
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  have hl : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |deriv (cgf X μ) x-deriv (cgf X μ) y| ≤ K*|x-y| := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.hasDerivAt.hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs,abs_of_nonneg (cgf_second_nonneg μ hX t)]; exact hbound t ht)
      (convex_Icc (0:ℝ) 1) hy hx
  have hip : IntervalIntegrable (fun t : ℝ => deriv (cgf X μ) (p*t)) volume 0 1 := by
    exact (hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => p*t))).intervalIntegrable 0 1
  have hiq : IntervalIntegrable (fun t : ℝ => deriv (cgf X μ) (q*t)) volume 0 1 := by
    exact (hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => q*t))).intervalIntegrable 0 1
  unfold entropicMean
  rw [← intervalIntegral.integral_sub hip hiq]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := K*|p-q|)
    (f := fun t => deriv (cgf X μ) (p*t)-deriv (cgf X μ) (q*t)) (by
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using (Set.Ioc_subset_Icc_self ht)
      have hpt : p*t ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg hp.1 ht'.1,
        (mul_le_mul hp.2 ht'.2 ht'.1 (by norm_num)).trans (by norm_num)⟩
      have hqt : q*t ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg hq.1 ht'.1,
        (mul_le_mul hq.2 ht'.2 ht'.1 (by norm_num)).trans (by norm_num)⟩
      have hh := hl _ hpt _ hqt
      rw [← sub_mul,abs_mul,abs_of_nonneg ht'.1] at hh
      apply hh.trans
      have := mul_le_mul_of_nonneg_left ht'.2 (mul_nonneg hK (abs_nonneg (p-q)))
      nlinarith)
  simpa using H

lemma cgf_second_le_of_moments
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {t c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hl : c ≤ mgf X μ t)
    (hu : (∫ ω, (X ω)^2*Real.exp (t*X ω) ∂μ) ≤ K) :
    deriv (deriv (cgf X μ)) t ≤ K/c := by
  have hh := iteratedDeriv_two_cgf (mem_interior_integrableExpSet_of_all μ hX t)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hh
  rw [hh]
  calc
    _ ≤ (∫ ω, (X ω)^2*Real.exp (t*X ω) ∂μ)/mgf X μ t := sub_le_self _ (sq_nonneg _)
    _ ≤ K/mgf X μ t := div_le_div_of_nonneg_right hu (mgf_pos (hX t)).le
    _ ≤ K/c := div_le_div_of_nonneg_left hK hc hl

end
end SphericalPerceptron
end
end

end OAI
