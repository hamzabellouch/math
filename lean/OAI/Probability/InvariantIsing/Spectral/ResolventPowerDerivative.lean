import OAI.Probability.InvariantIsing.Gaussian.MPDensityTransform
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Differentiation of bounded positive-resolvent moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace InvariantIsing

lemma positiveResolventTest_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => positiveResolventTest s x) (-(positiveResolventTest t x)^2) t := by
  have hn : t+max x 0 ≠ 0 := (add_pos_of_pos_of_nonneg ht (le_max_right x 0)).ne'
  convert ((hasDerivAt_id t).add_const (max x 0)).inv hn using 1
  · funext s
    simp only [positiveResolventTest,one_div,Pi.inv_apply,id_eq]
  · simp only [positiveResolventTest,div_eq_mul_inv,inv_pow,one_mul,id_eq,neg_mul]

lemma positiveResolventPower_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) (n : ℕ) :
    HasDerivAt (fun s => (positiveResolventTest s x)^n)
      (-(n : ℝ)*(positiveResolventTest t x)^(n+1)) t := by
  induction n with
  | zero => simpa only [pow_zero,Nat.cast_zero,neg_zero,zero_mul] using hasDerivAt_const t (1 : ℝ)
  | succ n ih =>
    convert ih.mul (positiveResolventTest_hasDerivAt ht x) using 1
    · funext s
      exact pow_succ _ _
    · simp only [Nat.cast_succ,pow_succ]
      ring

lemma positiveResolventPower_integrable {t : ℝ} (ht : 0 < t) (n : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x => (positiveResolventTest t x)^n) μ := by
  apply Integrable.of_bound ((continuous_positiveResolventTest ht).pow n).aestronglyMeasurable ((1/t)^n)
  exact ae_of_all _ fun x => by
    change ‖(positiveResolventTest t x)^n‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (positiveResolventTest_bound ht x).1 _)]
    exact pow_le_pow_left₀ (positiveResolventTest_bound ht x).1 (positiveResolventTest_bound ht x).2 n

theorem positiveResolventPower_integral_hasDerivAt (μ : Measure ℝ) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun s => ∫ x, (positiveResolventTest s x)^n ∂μ)
      (-(n : ℝ)*(∫ x, (positiveResolventTest t x)^(n+1) ∂μ)) t := by
  have hs : Ioi (t/2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x => (positiveResolventTest s x)^n) μ := by
    filter_upwards [hs] with s hs'
    exact ((continuous_positiveResolventTest (lt_trans (half_pos ht) hs')).pow n).aestronglyMeasurable
  have hd : ∀ᵐ x ∂μ, ∀ s ∈ Ioi (t/2),
      HasDerivAt (fun u => (positiveResolventTest u x)^n)
        (-(n : ℝ)*(positiveResolventTest s x)^(n+1)) s :=
    ae_of_all _ fun x s hs' => positiveResolventPower_hasDerivAt (lt_trans (half_pos ht) hs') x n
  have hb : ∀ᵐ x ∂μ, ∀ s ∈ Ioi (t/2),
      ‖-(n : ℝ)*(positiveResolventTest s x)^(n+1)‖ ≤ (n : ℝ)*(2/t)^(n+1) := by
    refine ae_of_all _ fun x s hs' => ?_
    have hsp : 0 < s := lt_trans (half_pos ht) hs'
    have hr : positiveResolventTest s x ≤ 2/t := by
      calc
        _ ≤ 1/s := (positiveResolventTest_bound hsp x).2
        _ ≤ 1/(t/2) := one_div_le_one_div_of_le (half_pos ht) hs'.le
        _ = 2/t := by ring
    rw [norm_mul,norm_neg,Real.norm_of_nonneg (Nat.cast_nonneg n),
      Real.norm_of_nonneg (pow_nonneg (positiveResolventTest_bound hsp x).1 _)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (positiveResolventTest_bound hsp x).1 hr _) (Nat.cast_nonneg n)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm
    (positiveResolventPower_integrable ht n μ)
    (((continuous_positiveResolventTest ht).pow (n+1)).const_mul (-(n : ℝ))).aestronglyMeasurable
    hb (integrable_const _) hd).2
  simpa only [integral_const_mul] using hh

end InvariantIsing

end

end OAI
