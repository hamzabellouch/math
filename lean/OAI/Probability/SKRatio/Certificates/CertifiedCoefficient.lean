import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarVariance
import OAI.Probability.SKRatio.Certificates.CertifiedFunctionBounds

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

lemma memLp_approxF (β A C : ℝ) : MemLp (approxF β A C) 2 (fieldLaw β) := by
  convert! (((((memLp_field_v β).add ((memLp_field β).const_mul A)).add
      (memLp_mv.const_mul (2*β^2))).add (memLp_v.const_mul
        (1/2-β^2*A/(64/100-(19/100)*A)))).add
      (memLp_m.const_mul (12/100:ℝ))).add (memLp_g.const_mul (3*β^2*C)) using 1
  ext h
  dsimp [approxF]
  ring

lemma sd_le_of_center {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) {c B : ℝ} (hB : 0 ≤ B)
    (hc : (∫ x, (f x-c)^2 ∂μ) ≤ B^2) : sd μ f ≤ B := by
  have ht := (sd_min_center hf c).trans hc
  nlinarith only [ht,sd_nonneg (μ := μ) f,hB]

lemma sd_unit {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) (hb : ∀ h, |f h| ≤ 1) : sd μ f ≤ 1 := by
  apply sd_le_of_center hf (c := 0) (by norm_num)
  simp only [sub_zero,one_pow]
  have ht := integral_mono hf.integrable_sq (integrable_const (μ := μ) (1:ℝ))
    (fun h => by nlinarith [hb h,sq_abs (f h),abs_nonneg (f h)])
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ht

lemma sd_field (β : ℝ) : sd (fieldLaw β) (fun h : ℝ => h) = |β| := by
  have hh := variance_id_gaussianReal (μ := β^2) (v := variance β)
  rw [variance_eq_integral measurable_id.aemeasurable] at hh
  change ∫ h, (h-(∫ t, t ∂fieldLaw β))^2 ∂fieldLaw β = _ at hh
  rw [variance_coe] at hh
  unfold sd l2Norm centered
  rw [hh,sqrt_sq_eq_abs]

lemma ratio_coefficient_error {A B : ℝ} (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) :
    |A/(64/100-(19/100)*A)-B/(64/100-(19/100)*B)| ≤ 4*|A-B| := by
  have hDA : 45/100 ≤ 64/100-(19/100)*A := by linarith
  have hDB : 45/100 ≤ 64/100-(19/100)*B := by linarith
  have hDA0 : 0 < 64/100-(19/100)*A := by linarith
  have hDB0 : 0 < 64/100-(19/100)*B := by linarith
  have he : A/(64/100-(19/100)*A)-B/(64/100-(19/100)*B) =
      (64/100)*(A-B)/((64/100-(19/100)*A)*(64/100-(19/100)*B)) := by
    rw [div_sub_div A B hDA0.ne' hDB0.ne']
    congr 1
    ring
  rw [he,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 64/100),
    abs_of_pos (mul_pos hDA0 hDB0)]
  apply (div_le_iff₀ (mul_pos hDA0 hDB0)).mpr
  have hp : (104/625:ℝ) ≤
      (64/100-(19/100)*A)*(64/100-(19/100)*B) := by
    nlinarith only [hA1,hB1,mul_nonneg hA hB]
  have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg (A-B))
  nlinarith only [hh,abs_nonneg (A-B)]

lemma approxF_error {β A C : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) :
    sd (fieldLaw β) (F β) ≤ sd (fieldLaw β) (approxF β A C)+
      2*|a β-A|+|G β-C| := by
  let ca := a β-A
  let cv := β^2*(A/(64/100-(19/100)*A)-a β/l β)
  let cg := 3*β^2*(G β-C)
  have he (h : ℝ) : F β h-approxF β A C h = ca*h+cv*v h+cg*g h := by
    dsimp [F,approxF,ca,cv,cg]
    ring
  have hi : MemLp (fun h : ℝ => ca*h) 2 (fieldLaw β) := (memLp_field β).const_mul ca
  have hiv : MemLp (fun h => cv*v h) 2 (fieldLaw β) := memLp_v.const_mul cv
  have hig : MemLp (fun h => cg*g h) 2 (fieldLaw β) := memLp_g.const_mul cg
  have h1 := sd_add hi hiv
  have h2 := sd_add (hi.add hiv) hig
  have hdiff := (le_abs_self _).trans (abs_sd_sub_le (memLp_F β) (memLp_approxF β A C))
  simp_rw [he] at hdiff
  have hid : sd (fieldLaw β) (fun h : ℝ => ca*h) = |ca| *β := by
    change sd (fieldLaw β) (fun h => ca*(fun t : ℝ => t) h) = _
    rw [sd_const_mul,sd_field,abs_of_nonneg hβ]
  simp only [Pi.add_def,sd_const_mul,hid] at h1 h2
  have hcv : |cv| ≤ |a β-A| := by
    have hh := ratio_coefficient_error (a_nonneg β) (a_le_one β) hA hA1
    rw [←l_eq,abs_sub_comm] at hh
    dsimp [cv]
    rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
    have hp := mul_le_mul_of_nonneg_left hh (sq_nonneg β)
    have hβ2 : β^2 ≤ (1/4:ℝ) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hβ2 (abs_nonneg (a β-A))
    nlinarith only [hp,hh']
  have hcg : |cg| ≤ |G β-C| := by
    dsimp [cg]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 3*β^2)]
    have hβ2 : 3*β^2 ≤ 1 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hβ2 (abs_nonneg (G β-C))]
  have hva := sd_unit (μ := fieldLaw β) memLp_v abs_v_le
  have hga := sd_unit (μ := fieldLaw β) memLp_g abs_g_le_one
  have hpv := mul_le_mul hcv hva (sd_nonneg (μ := fieldLaw β) v) (abs_nonneg (a β-A))
  have hpg := mul_le_mul hcg hga (sd_nonneg (μ := fieldLaw β) g) (abs_nonneg (G β-C))
  have hpa := mul_le_mul_of_nonneg_left hb (abs_nonneg ca)
  dsimp [ca] at h1 h2 hpa
  nlinarith only [hdiff,h1,h2,hpv,hpg,hpa,abs_nonneg (a β-A)]

end SKRatio.Certificate

end

end OAI
