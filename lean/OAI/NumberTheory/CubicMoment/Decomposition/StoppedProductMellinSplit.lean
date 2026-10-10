import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductMellinPhase

namespace OAI

/-! Exact smooth splitting of the complete Mellin line, with elementary
central and model-complement bounds. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma height_bump_norm (S t : ℝ) : ‖(heightPartitionBump (t/S):ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg heightPartitionBump.nonneg] using
    (heightPartitionBump.le_one (x := t/S))

lemma height_bump_complement_norm (S t : ℝ) :
    ‖(1:ℂ)-(heightPartitionBump (t/S):ℂ)‖ ≤ 1 := by
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sub_nonneg.mpr heightPartitionBump.le_one)]
  linarith [heightPartitionBump.nonneg (x := t/S)]

lemma smooth_height_integral_split (F : ℝ → ℂ) (hF : Integrable F) (S : ℝ) :
    (∫ t : ℝ, F t) =
      (∫ t : ℝ, (heightPartitionBump (t/S):ℂ)*F t)+
      ∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*F t := by
  have hb : Continuous (fun t : ℝ => (heightPartitionBump (t/S):ℂ)) :=
    Complex.continuous_ofReal.comp (heightPartitionBump.continuous.comp (continuous_id.div_const S))
  have h₁ : Integrable (fun t => (heightPartitionBump (t/S):ℂ)*F t) :=
    hF.bdd_mul hb.aestronglyMeasurable (Filter.Eventually.of_forall (height_bump_norm S))
  have h₂ : Integrable (fun t => (1-(heightPartitionBump (t/S):ℂ))*F t) :=
    hF.bdd_mul (continuous_const.sub hb).aestronglyMeasurable
      (Filter.Eventually.of_forall (height_bump_complement_norm S))
  rw [←integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards with t
  ring

lemma smooth_mellin_central_bound (w F : ℝ → ℂ) (hw : Integrable w)
    {S B : ℝ} (hS : 0 < S) (hB : 0 ≤ B)
    (hF : ∀ t, |t| ≤ (4/3)*S → ‖F t‖ ≤ B) :
    ‖∫ t : ℝ, (heightPartitionBump (t/S):ℂ)*w t*F t‖ ≤
      (∫ t : ℝ, ‖w t‖)*B := by
  rw [←integral_mul_const]
  apply norm_integral_le_of_norm_le (hw.norm.mul_const B)
  filter_upwards with t
  by_cases ht : |t| ≤ (4/3)*S
  · rw [norm_mul,norm_mul]
    exact mul_le_mul
      ((mul_le_mul_of_nonneg_right (height_bump_norm S t) (_root_.norm_nonneg _)).trans_eq (one_mul _))
      (hF t ht) (_root_.norm_nonneg _) (_root_.norm_nonneg _)
  · have hz : heightPartitionBump (t/S) = 0 := by
      apply heightPartitionBump_zero
      rw [abs_div,abs_of_pos hS]
      apply (le_div_iff₀ hS).mpr
      exact (lt_of_not_ge ht).le
    simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
    exact mul_nonneg (_root_.norm_nonneg _) hB

lemma smooth_mellin_model_tail_bound (w F : ℝ → ℂ) (q : ℕ)
    (hq : Integrable (fun t => |t|^q*‖w t‖))
    {S B : ℝ} (hS : 0 < S) (hB : 0 ≤ B) (hF : ∀ t, ‖F t‖ ≤ B) :
    ‖∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*w t*F t‖ ≤
      (B/S^q)*(∫ t : ℝ, |t|^q*‖w t‖) := by
  rw [←integral_const_mul]
  apply norm_integral_le_of_norm_le (hq.const_mul (B/S^q))
  filter_upwards with t
  by_cases ht : |t| ≤ S
  · have hz : heightPartitionBump (t/S) = 1 := by
      apply heightPartitionBump_one
      rw [abs_div,abs_of_pos hS]
      exact (div_le_one hS).mpr ht
    simp only [hz,Complex.ofReal_one,sub_self,zero_mul,norm_zero]
    positivity
  · have hts : S ≤ |t| := (lt_of_not_ge ht).le
    have hr : 1 ≤ |t|^q/S^q := (le_div_iff₀ (pow_pos hS q)).mpr
      (by simpa using pow_le_pow_left₀ hS.le hts q)
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*‖w t‖*B := mul_le_mul
        (mul_le_mul_of_nonneg_right (height_bump_complement_norm S t) (_root_.norm_nonneg _))
        (hF t) (_root_.norm_nonneg _) (by positivity)
      _ ≤ (|t|^q/S^q)*‖w t‖*B := by gcongr
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
