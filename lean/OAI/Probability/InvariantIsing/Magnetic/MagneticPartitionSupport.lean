import OAI.Probability.InvariantIsing.Magnetic.MagneticClosedSupport
import OAI.Probability.InvariantIsing.Magnetic.MagneticRefinement
import OAI.Probability.InvariantIsing.Fields.FieldPartitionSupport

namespace OAI

/-! The constrained scalar-field supporting inequality on arbitrary
finite partitions, expressed through the physical magnetic overlap path. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma magneticFieldPath_step_ae (h : FieldStep) (m : ℝ) :
    (magneticFieldPath h m).val =ᵐ[pathMeasure]
      finiteStepFunction h.cut (magneticFieldLevel h m) := by
  filter_upwards [ae_finite_overlap_cell h.cut h.first h.last] with s hs
  obtain ⟨i, hi⟩ := hs
  rw [magneticFieldPath_on_cell h m i hi,
    finiteStepFunction_on_cell h.ordered_cut _ hi]

lemma fieldPairing_magnetic_same (h : FieldStep) (m : ℝ)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldPairing (magneticFieldPath h m) (fieldWithHeights h r hr0 hrmono) =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * r i := by
  change (∫ s, magneticFieldPath h m s * fieldFunction (fieldWithHeights h r hr0 hrmono) s
    ∂pathMeasure) = _
  calc
    _ = ∫ s, finiteStepFunction h.cut (magneticFieldLevel h m) s *
        finiteStepFunction h.cut r s ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [magneticFieldPath_step_ae h m] with s hs
      rw [hs]
      rfl
    _ = _ := integral_finiteStepFunction_mul h.cut h.ordered_cut h.first h.last _ _

lemma fieldPairing_magnetic_self (h : FieldStep) (m : ℝ) :
    fieldPairing (magneticFieldPath h m) h =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * h.height i := by
  have he : fieldWithHeights h h.height h.nonneg h.ordered_height = h := by
    cases h
    rfl
  simpa only [he] using fieldPairing_magnetic_same h m h.height h.nonneg h.ordered_height

lemma magneticField_support_same_partition (h : FieldStep) {m : ℝ} (hm : |m| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    constrainedFieldValue (fieldWithHeights h r hr0 hrmono) m ≤ constrainedFieldValue h m -
      (1 / 2 : ℝ) * ∫ s, magneticFieldPath h m s *
        (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure := by
  have hi := magneticHeight_support h hm r hr0 hrmono
  have he : (∫ s, magneticFieldPath h m s *
      (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure) =
      fieldPairing (magneticFieldPath h m) (fieldWithHeights h r hr0 hrmono) -
        fieldPairing (magneticFieldPath h m) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he, fieldPairing_magnetic_same, fieldPairing_magnetic_self]
  have hsum : (∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * magneticFieldLevel h m i) *
      (r i - h.height i)) = -(1 / 2 : ℝ) *
        ((∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * r i) -
          ∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * h.height i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hi
  linarith

lemma magneticField_support_equal_cutList {h k : FieldStep} {m : ℝ} (hm : |m| < 1)
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    constrainedFieldValue k m ≤ constrainedFieldValue h m - (1 / 2 : ℝ) *
      ∫ s, magneticFieldPath h m s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨r, hr0, hrmono, rfl⟩ := field_eq_withHeights_of_cutList he
  exact magneticField_support_same_partition h hm r hr0 hrmono

theorem magneticField_support (h k : FieldStep) {m : ℝ} (hm : |m| < 1) :
    constrainedFieldValue k m ≤ constrainedFieldValue h m - (1 / 2 : ℝ) *
      ∫ s, magneticFieldPath h m s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨h', k', hh', hk', hcuts⟩ := field_common_refinement h k
  have hi := magneticField_support_equal_cutList hm hcuts
  rw [hh'.constrainedValue m, hk'.constrainedValue m] at hi
  have he : (∫ s, magneticFieldPath h' m s * (fieldFunction k' s - fieldFunction h' s)
      ∂pathMeasure) = ∫ s, magneticFieldPath h m s *
        (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
    apply integral_congr_ae
    filter_upwards [hh'.magneticPath_ae m, hh'.field_ae, hk'.field_ae] with s hB hh hk
    rw [hB, hh, hk]
  rwa [he] at hi

theorem magneticField_support_pairing (h k : FieldStep) {m : ℝ} (hm : |m| < 1) :
    constrainedFieldValue k m + (1 / 2 : ℝ) * fieldPairing (magneticFieldPath h m) k ≤
      constrainedFieldValue h m + (1 / 2 : ℝ) * fieldPairing (magneticFieldPath h m) h := by
  have hs := magneticField_support h k hm
  have he : (∫ s, magneticFieldPath h m s * (fieldFunction k s - fieldFunction h s)
      ∂pathMeasure) = fieldPairing (magneticFieldPath h m) k -
        fieldPairing (magneticFieldPath h m) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he] at hs
  linarith

end InvariantIsing

end

end OAI
