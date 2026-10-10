import Mathlib
import OAI.Analysis.CoulombIonization.Localization.QuantumRawLaw

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationSmooth_scope

open MeasureTheory Set
open scoped ContDiff

lemma compactNoiseWeight_eq_glue (u : ℝ) :
    compactNoiseWeight u = expNegInvGlue (1-u^2) := by
  have hh : |u| < 1 ↔ ¬ 1-u^2 ≤ 0 := by
    rw [not_le, sub_pos, sq_lt_one_iff_abs_lt_one]
  simp only [compactNoiseWeight, expNegInvGlue, hh]
  split_ifs <;> rfl

lemma compactNoiseWeight_contDiff {n : ℕ∞} : ContDiff ℝ n compactNoiseWeight := by
  simp_rw [funext compactNoiseWeight_eq_glue]
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

lemma compactNoiseDensity_contDiff {n : ℕ∞} : ContDiff ℝ n compactNoiseDensity :=
  contDiff_const.mul compactNoiseWeight_contDiff

lemma compactNoiseWeight_hasDerivAt (u : ℝ) :
    HasDerivAt compactNoiseWeight (compactNoiseScore u * compactNoiseWeight u) u := by
  have hc : HasDerivAt expNegInvGlue ((1-u^2)⁻¹^2 * expNegInvGlue (1-u^2)) (1-u^2) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 (1-u^2)
  have hh := hc.comp u ((hasDerivAt_const u 1).sub ((hasDerivAt_id u).pow 2))
  simp only [Nat.cast_ofNat, mul_one, zero_sub, id_eq, Nat.reduceSub, pow_one] at hh
  have he : ((((1-u^2)⁻¹^2 * expNegInvGlue (1-u^2)) * -(2*u))) =
      compactNoiseScore u * compactNoiseWeight u := by
    rw [← compactNoiseWeight_eq_glue]
    by_cases hu : |u| < 1
    · simp only [compactNoiseScore, ite_eq_left hu, div_eq_mul_inv, inv_pow]; ring
    · simp [compactNoiseScore, compactNoiseWeight, hu]
  rw [he] at hh
  simpa only [Function.comp_def, Pi.sub_apply, Pi.pow_apply, id_eq, ← compactNoiseWeight_eq_glue] using hh

lemma compactNoiseDensity_hasDerivAt (u : ℝ) :
    HasDerivAt compactNoiseDensity (compactNoiseScore u * compactNoiseDensity u) u := by
  convert! (compactNoiseWeight_hasDerivAt u).const_mul compactNoiseNormalizer using 1
  dsimp [compactNoiseDensity]
  ring

lemma compactNoiseWeight_compactSupport : HasCompactSupport compactNoiseWeight := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
  intro u hu
  have hh : ¬ |u| < 1 := by
    intro h
    apply hu
    exact ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
  simp [compactNoiseWeight, hh]

lemma compactNoiseDensity_compactSupport : HasCompactSupport compactNoiseDensity :=
  compactNoiseWeight_compactSupport.mul_left

end Work_ObservationSmooth_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def compactNoiseKernel {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  ∏ i, compactNoiseDensity (u i)

lemma compactNoiseKernel_nonneg {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    0 ≤ compactNoiseKernel u := prod_nonneg (fun _ _ => compactNoiseDensity_nonneg _)

lemma compactNoiseKernel_even {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    compactNoiseKernel (-u) = compactNoiseKernel u := by
  simp only [compactNoiseKernel, Pi.neg_apply, compactNoiseDensity, compactNoiseWeight_even]

lemma compactNoiseKernel_contDiff {ι : Type*} [Fintype ι] {n : ℕ∞} :
    ContDiff ℝ n (compactNoiseKernel : (ι → ℝ) → ℝ) := by
  exact contDiff_prod (fun i _ => compactNoiseDensity_contDiff.comp (contDiff_apply ℝ ℝ i))

lemma compactNoiseKernel_integrable {ι : Type*} [Fintype ι] :
    Integrable (compactNoiseKernel : (ι → ℝ) → ℝ) := by
  exact Integrable.fintype_prod (fun _ => compactNoiseDensity_integrable)

lemma compactNoiseKernel_compactSupport {ι : Type*} [Fintype ι] :
    HasCompactSupport (compactNoiseKernel : (ι → ℝ) → ℝ) := by
  classical
  apply HasCompactSupport.intro (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (-1:ℝ)) (b := 1)))
  intro u hu
  simp only [mem_univ_pi] at hu
  push Not at hu
  obtain ⟨i, hi⟩ := hu
  apply prod_eq_zero (mem_univ i)
  have hh : ¬|u i| < 1 := by
    intro h
    exact hi ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
  simp [compactNoiseDensity, compactNoiseWeight, hh]

lemma compactNoiseLaw_apply {s : Set ℝ} (hs : MeasurableSet s) :
    compactNoiseLaw s = ENNReal.ofReal (∫ u in s, compactNoiseDensity u) := by
  rw [compactNoiseLaw, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal compactNoiseDensity_integrable.integrableOn
    (ae_of_all _ compactNoiseDensity_nonneg)).symm

lemma compactNoiseLaw_pi {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => compactNoiseLaw) =
      volume.withDensity (fun u : ι → ℝ => ENNReal.ofReal (compactNoiseKernel u)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal compactNoiseKernel_integrable.integrableOn
      (ae_of_all _ compactNoiseKernel_nonneg)]
  simp only [volume_pi, Measure.restrict_pi_pi, compactNoiseKernel,
    integral_fintype_prod_eq_prod, compactNoiseLaw_apply (hs _)]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg (fun _ => compactNoiseDensity_nonneg _))

lemma compactNoiseLaw_pi_integral {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) :
    (∫ u, f u ∂Measure.pi (fun _ : ι => compactNoiseLaw)) =
      ∫ u, compactNoiseKernel u * f u := by
  rw [compactNoiseLaw_pi, integral_withDensity_eq_integral_toReal_smul
    (compactNoiseKernel_contDiff (n := 0)).continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (compactNoiseKernel_nonneg _), smul_eq_mul]

lemma compactNoiseKernel_hasFDerivAt {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    HasFDerivAt compactNoiseKernel
      (∑ i, (compactNoiseScore (u i) * compactNoiseKernel u) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) u := by
  classical
  have hi (i : ι) : HasFDerivAt (fun v : ι → ℝ => compactNoiseDensity (v i))
      ((compactNoiseScore (u i) * compactNoiseDensity (u i)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) u :=
    by
      convert! HasDerivAt.comp_hasFDerivAt (f := fun v : ι → ℝ => v i) u
        (compactNoiseDensity_hasDerivAt (u i)) (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt using 1
  convert! HasFDerivAt.finsetProd (u := univ) (fun i _ => hi i) using 1
  apply sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  rw [mul_left_comm, prod_erase_mul _ _ (mem_univ i)]
  rfl

lemma compactNoiseKernel_fderiv_apply {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    fderiv ℝ compactNoiseKernel u v =
      compactNoiseKernel u * ∑ i, compactNoiseScore (u i) * v i := by
  rw [(compactNoiseKernel_hasFDerivAt u).fderiv]
  simp only [_root_.sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

end CoulombObservation

end

end OAI
