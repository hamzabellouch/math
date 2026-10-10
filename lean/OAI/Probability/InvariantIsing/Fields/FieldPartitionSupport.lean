import OAI.Probability.InvariantIsing.Fields.FieldCommonRefinement
import OAI.Probability.InvariantIsing.Fields.FieldHeightClosedSupport

namespace OAI

/-! The scalar-field supporting inequality, independent of the finite partition. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldMagnetizationPath_step_ae (h : FieldStep) :
    (fieldMagnetizationPath h).val =ᵐ[pathMeasure]
      finiteStepFunction h.cut (fieldMagnetizationLevel h) := by
  filter_upwards [ae_finite_overlap_cell h.cut h.first h.last] with s hs
  obtain ⟨i, hi⟩ := hs
  rw [fieldMagnetizationPath_on_cell h i hi,
    finiteStepFunction_on_cell h.ordered_cut _ hi]

lemma fieldPairing_magnetization_same (h : FieldStep)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldPairing (fieldMagnetizationPath h) (fieldWithHeights h r hr0 hrmono) =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * r i := by
  change (∫ s, fieldMagnetizationPath h s * fieldFunction (fieldWithHeights h r hr0 hrmono) s
    ∂pathMeasure) = _
  calc
    _ = ∫ s, finiteStepFunction h.cut (fieldMagnetizationLevel h) s *
        finiteStepFunction h.cut r s ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [fieldMagnetizationPath_step_ae h] with s hs
      rw [hs]
      rfl
    _ = _ := integral_finiteStepFunction_mul h.cut h.ordered_cut h.first h.last _ _

lemma fieldPairing_magnetization_self (h : FieldStep) :
    fieldPairing (fieldMagnetizationPath h) h =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * h.height i := by
  have he : fieldWithHeights h h.height h.nonneg h.ordered_height = h := by
    cases h
    rfl
  simpa only [he] using fieldPairing_magnetization_same h h.height h.nonneg h.ordered_height

lemma field_support_same_partition (h : FieldStep)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldValue (fieldWithHeights h r hr0 hrmono) 0 ≤ fieldValue h 0 -
      (1 / 2 : ℝ) * ∫ s, fieldMagnetizationPath h s *
        (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure := by
  have hi := fieldHeight_support h r hr0 hrmono
  have he : (∫ s, fieldMagnetizationPath h s *
      (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure) =
      fieldPairing (fieldMagnetizationPath h) (fieldWithHeights h r hr0 hrmono) -
        fieldPairing (fieldMagnetizationPath h) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he, fieldPairing_magnetization_same, fieldPairing_magnetization_self]
  have hs : (∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * fieldMagnetizationLevel h i) *
      (r i - h.height i)) = -(1 / 2 : ℝ) *
        ((∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * r i) -
          ∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * h.height i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs] at hi
  linarith

lemma field_eq_withHeights_of_cutList {h k : FieldStep}
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    ∃ (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r),
      k = fieldWithHeights h r hr0 hrmono := by
  have hl := congrArg List.length he
  simp only [List.length_ofFn] at hl
  have hd : h.depth = k.depth := by omega
  rcases h with ⟨n, cut, hcut, hfirst, hlast, v, hv0, hvm⟩
  rcases k with ⟨m, cut', hcut', hfirst', hlast', w, hw0, hwm⟩
  dsimp only at hd
  subst m
  have hcut_eq : cut = cut' := List.ofFn_injective he
  subst cut'
  exact ⟨w, hw0, hwm, rfl⟩

lemma field_support_equal_cutList {h k : FieldStep}
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    fieldValue k 0 ≤ fieldValue h 0 - (1 / 2 : ℝ) *
      ∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨r, hr0, hrmono, rfl⟩ := field_eq_withHeights_of_cutList he
  exact field_support_same_partition h r hr0 hrmono

/-- The exact scalar supporting inequality for arbitrary finite field partitions. -/
theorem field_support (h k : FieldStep) :
    fieldValue k 0 ≤ fieldValue h 0 - (1 / 2 : ℝ) *
      ∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨h', k', hh', hk', hcuts⟩ := field_common_refinement h k
  have hi := field_support_equal_cutList hcuts
  rw [hh'.value, hk'.value] at hi
  have he : (∫ s, fieldMagnetizationPath h' s * (fieldFunction k' s - fieldFunction h' s)
      ∂pathMeasure) = ∫ s, fieldMagnetizationPath h s *
        (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
    apply integral_congr_ae
    filter_upwards [hh'.magnetization_ae, hh'.field_ae, hk'.field_ae] with s hB hh hk
    rw [hB, hh, hk]
  rwa [he] at hi

end InvariantIsing

end

end OAI
