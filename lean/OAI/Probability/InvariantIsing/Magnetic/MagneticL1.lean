import OAI.Probability.InvariantIsing.Magnetic.MagneticClosedLipschitz
import OAI.Probability.InvariantIsing.Magnetic.MagneticRefinement
import OAI.Probability.InvariantIsing.Fields.FieldPartitionSupport

namespace OAI

/-! The constrained field functional is one-half Lipschitz in the L1
distance between arbitrary bounded monotone field paths. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma field_height_difference_integral (h : FieldStep)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    (∫ t, |fieldFunction (fieldWithHeights h r hr0 hrmono) t - fieldFunction h t| ∂pathMeasure) =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * |r i - h.height i| := by
  calc
    _ = ∫ t, finiteStepFunction h.cut (fun i => |r i - h.height i|) t ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_finite_overlap_cell h.cut h.first h.last] with t ht
      obtain ⟨i, hi⟩ := ht
      change |finiteStepFunction h.cut r t - finiteStepFunction h.cut h.height t| = _
      rw [finiteStepFunction_on_cell h.ordered_cut _ hi,
        finiteStepFunction_on_cell h.ordered_cut _ hi,
        finiteStepFunction_on_cell h.ordered_cut _ hi]
    _ = _ := integral_finiteStepFunction h.cut h.ordered_cut h.first h.last _

lemma constrainedFieldValue_lipschitz_equal_cutList {h k : FieldStep} {s : ℝ} (hs : |s| < 1)
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    |constrainedFieldValue k s - constrainedFieldValue h s| ≤
      (1 / 2 : ℝ) * ∫ t, |fieldFunction k t - fieldFunction h t| ∂pathMeasure := by
  obtain ⟨r, hr0, hrmono, rfl⟩ := field_eq_withHeights_of_cutList he
  rw [field_height_difference_integral]
  exact constrainedFieldValue_height_lipschitz h hs r hr0 hrmono

theorem abs_constrainedFieldValue_sub_le_L1 (h k : FieldStep) {s : ℝ} (hs : |s| < 1) :
    |constrainedFieldValue k s - constrainedFieldValue h s| ≤
      (1 / 2 : ℝ) * ∫ t, |fieldFunction k t - fieldFunction h t| ∂pathMeasure := by
  obtain ⟨h', k', hh', hk', hcuts⟩ := field_common_refinement h k
  have hi := constrainedFieldValue_lipschitz_equal_cutList hs hcuts
  rw [hh'.constrainedValue, hk'.constrainedValue] at hi
  have he : (∫ t, |fieldFunction k' t - fieldFunction h' t| ∂pathMeasure) =
      ∫ t, |fieldFunction k t - fieldFunction h t| ∂pathMeasure := by
    apply integral_congr_ae
    filter_upwards [hh'.field_ae, hk'.field_ae] with t hh hk
    rw [hh, hk]
  rwa [he] at hi

lemma constrainedFieldValue_eq_of_ae (h k : FieldStep) {s : ℝ} (hs : |s| < 1)
    (he : fieldFunction h =ᵐ[pathMeasure] fieldFunction k) :
    constrainedFieldValue h s = constrainedFieldValue k s := by
  have hb := abs_constrainedFieldValue_sub_le_L1 h k hs
  have hz : (∫ t, |fieldFunction k t - fieldFunction h t| ∂pathMeasure) = 0 := by
    calc
      _ = ∫ _t : ℝ, (0 : ℝ) ∂pathMeasure := by
        apply integral_congr_ae
        filter_upwards [he] with t ht
        rw [ht, sub_self, abs_zero]
      _ = 0 := integral_zero _ _
  rw [hz, mul_zero] at hb
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))).symm

end InvariantIsing

end

end OAI
