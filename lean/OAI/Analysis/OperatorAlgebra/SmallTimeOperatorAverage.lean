import OAI.Analysis.ModularRecovery.StrongIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace OAI

/-! Strong convergence of normalized small-time operator averages. This
supplies the regularization limit in the modular commutation argument. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WeakPureInfiniteness

def realGaussianDensity (t : ℝ) : ℝ := Real.exp (-t ^ 2) / Real.sqrt Real.pi

lemma realGaussianDensity_nonneg (t : ℝ) : 0 ≤ realGaussianDensity t := by
  exact div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

lemma realGaussianDensity_integrable : Integrable realGaussianDensity := by
  change Integrable (fun t : ℝ => Real.exp (-t ^ 2) / Real.sqrt Real.pi)
  have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).div_const
    (Real.sqrt Real.pi)
  simpa only [one_mul, neg_mul] using h

lemma realGaussianDensity_integral : ∫ t, realGaussianDensity t = 1 := by
  unfold realGaussianDensity
  rw [integral_div]
  have he : ∫ t : ℝ, Real.exp (-t ^ 2) = Real.sqrt Real.pi := by
    simpa only [neg_mul, one_mul, div_one] using integral_gaussian (1 : ℝ)
  rw [he, div_self (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))]

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]

def smallTimeOperatorAverage (V : ℝ → K →L[ℂ] K)
    (hc : ∀ x, Continuous (fun t => V t x)) (C : ℝ) (hC : ∀ t, ‖V t‖ ≤ C) (n : ℕ) :
    K →L[ℂ] K :=
  BoundedRecovery.strongIntegral (fun t => (realGaussianDensity t : ℂ))
    realGaussianDensity_integrable.ofReal (fun t => V (t / (n + 1 : ℝ)))
    (fun x => (hc x).comp (continuous_id.div_const _)) C (fun _ => hC _)

omit [CompleteSpace K] in
lemma smallTimeOperatorAverage_norm_le (V : ℝ → K →L[ℂ] K)
    (hc : ∀ x, Continuous (fun t => V t x)) (C : ℝ) (hC : ∀ t, ‖V t‖ ≤ C) (n : ℕ) :
    ‖smallTimeOperatorAverage V hc C hC n‖ ≤ C := by
  have hd : (∫ t : ℝ, ‖(realGaussianDensity t : ℂ)‖) = 1 := by
    have he : (fun t : ℝ => ‖(realGaussianDensity t : ℂ)‖) = realGaussianDensity := by
      funext t
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (realGaussianDensity_nonneg t)]
    rw [he, realGaussianDensity_integral]
  have hn := BoundedRecovery.norm_strongIntegral_le
    (fun t => (realGaussianDensity t : ℂ)) realGaussianDensity_integrable.ofReal
    (fun t => V (t / (n + 1 : ℝ)))
    (fun x => (hc x).comp (continuous_id.div_const _))
    ((norm_nonneg (V 0)).trans (hC 0)) (fun _ => hC _)
  rw [hd, one_mul] at hn
  exact hn

lemma smallTimeOperatorAverage_strong (V : ℝ → K →L[ℂ] K)
    (hc : ∀ x, Continuous (fun t => V t x)) (C : ℝ) (hC : ∀ t, ‖V t‖ ≤ C) (x : K) :
    Tendsto (fun n => smallTimeOperatorAverage V hc C hC n x) atTop (𝓝 (V 0 x)) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun t : ℝ => (realGaussianDensity t : ℂ) • V (t / (n + 1 : ℝ)) x) volume := by
    exact realGaussianDensity_integrable.ofReal.aestronglyMeasurable.smul
      ((hc x).comp (continuous_id.div_const _)).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ t : ℝ, ‖(realGaussianDensity t : ℂ) • V (t / (n + 1 : ℝ)) x‖ ≤
      realGaussianDensity t * (C * ‖x‖) := by
    filter_upwards [] with t
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (realGaussianDensity_nonneg t)]
    exact mul_le_mul_of_nonneg_left
      (((V _).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg x)))
      (realGaussianDensity_nonneg t)
  have hp : ∀ᵐ t : ℝ, Tendsto
      (fun n : ℕ => (realGaussianDensity t : ℂ) • V (t / (n + 1 : ℝ)) x) atTop
      (𝓝 ((realGaussianDensity t : ℂ) • V 0 x)) := by
    filter_upwards [] with t
    have ht : Tendsto (fun n : ℕ => t / (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
    exact ((hc x).continuousAt.tendsto.comp ht).const_smul _
  have hi := tendsto_integral_of_dominated_convergence
    (fun t => realGaussianDensity t * (C * ‖x‖)) hm
    (realGaussianDensity_integrable.mul_const _) hb hp
  have he : (∫ t : ℝ, (realGaussianDensity t : ℂ) • V 0 x) = V 0 x := by
    rw [integral_smul_const]
    have hi : (∫ t : ℝ, (realGaussianDensity t : ℂ)) = 1 :=
      (integral_ofReal (𝕜 := ℂ) (μ := volume) (f := realGaussianDensity)).trans
        (by rw [realGaussianDensity_integral]; rfl)
    rw [hi, one_smul]
  simpa only [smallTimeOperatorAverage, BoundedRecovery.strongIntegral_apply, he] using hi

end WeakPureInfiniteness

end

end OAI
