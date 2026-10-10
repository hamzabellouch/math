import OAI.Probability.InvariantIsing.Fields.FieldPartitionSupport

namespace OAI

/-! The scalar value is one-half Lipschitz in the L1 distance of finite field paths. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

lemma field_weighted_difference_bound (p : OverlapPath) (h k : FieldStep) :
    |∫ s, p s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure| ≤
      ∫ s, |fieldFunction k s - fieldFunction h s| ∂pathMeasure := by
  have hi : Integrable (fun s => p s * (fieldFunction k s - fieldFunction h s)) pathMeasure := by
    apply ((integrable_path_mul_field p k).sub (integrable_path_mul_field p h)).congr
    filter_upwards [] with s
    change p s * fieldFunction k s - p s * fieldFunction h s =
      p s * (fieldFunction k s - fieldFunction h s)
    ring
  have hd := (integrable_fieldFunction k).sub (integrable_fieldFunction h)
  calc
    _ ≤ ∫ s, |p s * (fieldFunction k s - fieldFunction h s)| ∂pathMeasure := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun s => p s * (fieldFunction k s - fieldFunction h s))
    _ ≤ _ := integral_mono_ae hi.norm hd.norm (by
      filter_upwards [] with s
      change |p s * (fieldFunction k s - fieldFunction h s)| ≤
        |fieldFunction k s - fieldFunction h s|
      rw [abs_mul, abs_of_nonneg (p.nonneg s)]
      exact mul_le_of_le_one_left (abs_nonneg _) (p.le_one s))

/-- Uniform in the sizes and relative positions of the two finite partitions. -/
theorem abs_fieldValue_sub_le_L1 (h k : FieldStep) :
    |fieldValue k 0 - fieldValue h 0| ≤
      (1 / 2 : ℝ) * ∫ s, |fieldFunction k s - fieldFunction h s| ∂pathMeasure := by
  have hk := field_support h k
  have kh := field_support k h
  have hb := field_weighted_difference_bound (fieldMagnetizationPath h) h k
  have hc := field_weighted_difference_bound (fieldMagnetizationPath k) k h
  have he : (∫ s, |fieldFunction h s - fieldFunction k s| ∂pathMeasure) =
      ∫ s, |fieldFunction k s - fieldFunction h s| ∂pathMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => abs_sub_comm _ _)
  rw [he] at hc
  rw [abs_le] at hb hc ⊢
  constructor <;> linarith

lemma fieldValue_eq_of_ae (h k : FieldStep)
    (he : fieldFunction h =ᵐ[pathMeasure] fieldFunction k) :
    fieldValue h 0 = fieldValue k 0 := by
  have hb := abs_fieldValue_sub_le_L1 h k
  have hz : (∫ s, |fieldFunction k s - fieldFunction h s| ∂pathMeasure) = 0 := by
    calc
      _ = ∫ _s : ℝ, (0 : ℝ) ∂pathMeasure := by
        apply integral_congr_ae
        filter_upwards [he] with s hs
        rw [hs, sub_self, abs_zero]
      _ = 0 := integral_zero _ _
  rw [hz, mul_zero] at hb
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))).symm

end InvariantIsing

end

end OAI
