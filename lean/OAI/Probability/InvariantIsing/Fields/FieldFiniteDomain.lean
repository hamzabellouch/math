import OAI.Probability.InvariantIsing.Fields.FieldMajorantFold

namespace OAI

/-! Finite-step entropy is finite for trial paths bounded strictly below one. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma measurable_fieldFunction (h : FieldStep) : Measurable (fieldFunction h) :=
  IsingPerceptron.measurable_finiteStepFunction h.cut h.height

lemma fieldFunction_le_last (h : FieldStep) (s : ℝ) :
    fieldFunction h s ≤ h.height (Fin.last h.depth) := by
  classical
  by_cases hex : ∃ i : Fin (h.depth + 1), h.cut i.castSucc < s ∧ s < h.cut i.succ
  · obtain ⟨i, hi⟩ := hex
    have he := IsingPerceptron.finiteStepFunction_on_cell h.ordered_cut h.height hi
    change IsingPerceptron.finiteStepFunction h.cut h.height s ≤ _
    rw [he]
    exact h.ordered_height (Fin.le_last _)
  · have he : fieldFunction h s = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hex ⟨i, hi⟩)
    rw [he]
    exact h.nonneg _

lemma integrable_fieldFunction (h : FieldStep) : Integrable (fieldFunction h) pathMeasure := by
  apply (integrable_const (h.height (Fin.last h.depth))).mono'
    (measurable_fieldFunction h).aestronglyMeasurable
  filter_upwards [] with s
  simpa only [Real.norm_eq_abs, abs_of_nonneg (fieldFunction_nonneg h s)] using
    fieldFunction_le_last h s

lemma integrable_path_mul_field (p : OverlapPath) (h : FieldStep) :
    Integrable (fun s => p s * fieldFunction h s) pathMeasure := by
  apply (integrable_fieldFunction h).mono'
    (p.measurable.mul (measurable_fieldFunction h)).aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (p.nonneg s),
    abs_of_nonneg (fieldFunction_nonneg h s)]
  exact mul_le_of_le_one_left (fieldFunction_nonneg h s) (p.le_one s)

lemma integral_fieldFunction (h : FieldStep) :
    (∫ s, fieldFunction h s ∂pathMeasure) =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * h.height i :=
  IsingPerceptron.integral_finiteStepFunction h.cut h.ordered_cut h.first h.last h.height

/-- Summation by parts for the finite height increments. -/
lemma sum_finite_height_difference (n : ℕ) (H F : ℕ → ℝ) :
    (∑ i : Fin (n + 1), (H i - if i.val = 0 then 0 else H (i.val - 1)) * F i) =
      H n * F n + ∑ i : Fin n, H i * (F i - F (i.val + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.succ_ne_zero, ite_false,
      Nat.add_sub_cancel]
    rw [ih]
    ring

lemma fieldIncrement_eq_heightSequence (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fieldIncrement h i).2 = heightSequence h i -
      if i.val = 0 then 0 else heightSequence h (i.val - 1) := by
  rw [heightSequence_eq h _ (by omega)]
  unfold fieldIncrement
  split_ifs with hi
  · rfl
  · rw [heightSequence_eq h _ (by omega)]

/-- A clamped extension used only to express finite summation by parts. -/
def fieldCutSequence (h : FieldStep) (i : ℕ) : ℝ :=
  h.cut ⟨min i (h.depth + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma fieldCutSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth + 1) :
    fieldCutSequence h i = h.cut ⟨i, by omega⟩ := by
  simp only [fieldCutSequence, min_eq_left hi]

lemma fieldIncrement_weighted_sum (h : FieldStep) (F : ℝ → ℝ) :
    (∑ i : Fin (h.depth + 1), (fieldIncrement h i).2 * F (h.cut i.castSucc)) =
      h.height (Fin.last h.depth) * F (h.cut (Fin.last h.depth).castSucc) +
        ∑ i : Fin h.depth, h.height i.castSucc *
          (F (h.cut i.castSucc.castSucc) - F (h.cut i.succ.castSucc)) := by
  have hs := sum_finite_height_difference h.depth (heightSequence h)
    (fun i => F (fieldCutSequence h i))
  convert hs using 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [fieldIncrement_eq_heightSequence, fieldCutSequence_eq h _ (by omega)]
    rfl
  · congr 1
    · rw [heightSequence_eq h _ le_rfl, fieldCutSequence_eq h _ (by omega)]
      rfl
    · apply Finset.sum_congr rfl
      intro i _
      rw [heightSequence_eq h _ (by omega), fieldCutSequence_eq h _ (by omega),
        fieldCutSequence_eq h _ (by omega)]
      rfl

lemma integral_fieldFunction_eq_increment_sum (h : FieldStep) :
    (∫ s, fieldFunction h s ∂pathMeasure) =
      ∑ i : Fin (h.depth + 1), (1 - h.cut i.castSucc) * (fieldIncrement h i).2 := by
  rw [integral_fieldFunction]
  have hs := fieldIncrement_weighted_sum h (fun x => 1 - x)
  rw [Fin.sum_univ_castSucc] at ⊢
  rw [show h.cut (Fin.last h.depth).succ = 1 from h.last]
  rw [show (∑ i : Fin (h.depth + 1),
      (1 - h.cut i.castSucc) * (fieldIncrement h i).2) =
      ∑ i : Fin (h.depth + 1), (fieldIncrement h i).2 * (1 - h.cut i.castSucc) by
        apply Finset.sum_congr rfl; intro i _; ring, hs]
  have heq :
      (∑ i : Fin h.depth,
        (h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) * h.height i.castSucc) =
      ∑ i : Fin h.depth, h.height i.castSucc *
        ((1 - h.cut i.castSucc.castSucc) - (1 - h.cut i.succ.castSucc)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.castSucc.succ = i.succ.castSucc := by ext; rfl
    rw [hi]
    ring
  rw [heq]
  ring

lemma fieldIncrement_sum (h : FieldStep) :
    (∑ i : Fin (h.depth + 1), (fieldIncrement h i).2) =
      h.height (Fin.last h.depth) := by
  simpa using fieldIncrement_weighted_sum h (fun _ => 1)

lemma fieldPairing_le_const_integral (p : OverlapPath) (h : FieldStep) (m : ℝ)
    (hp : ∀ᵐ s ∂pathMeasure, p s ≤ m) :
    fieldPairing p h ≤ m * ∫ s, fieldFunction h s ∂pathMeasure := by
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_path_mul_field p h)
    ((integrable_fieldFunction h).const_mul m)
  filter_upwards [hp] with s hs
  exact mul_le_mul_of_nonneg_right hs (fieldFunction_nonneg h s)

lemma field_majorant_coefficient_le_one {d c : ℝ} (hd : d ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    max c d + (1 - d) * (1 - c) ≤ 1 := by
  rcases le_total c d with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd.2) hc.1]
  · rw [max_eq_left h]
    nlinarith [mul_nonneg hd.1 (sub_nonneg.mpr hc.2)]

/-- The exact entropy cap needed for finite-step trial paths below one. -/
lemma fieldValue_add_pairing_le (p : OverlapPath) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hp : ∀ᵐ s ∂pathMeasure, p s ≤ 1 - d) (h : FieldStep) :
    fieldValue h 0 + fieldPairing p h / 2 ≤ (d⁻¹ - 1) * Real.log 2 := by
  have hv := fieldValue_majorant_sum h hd hd1 0
  rw [fieldMajorant_zero, List.map_ofFn, List.sum_ofFn] at hv
  simp only [Function.comp_def] at hv
  have hp' := fieldPairing_le_const_integral p h (1 - d) hp
  rw [integral_fieldFunction_eq_increment_sum] at hp'
  have hsum : (∑ i : Fin (h.depth + 1),
      (max (h.cut i.castSucc) d + (1 - d) * (1 - h.cut i.castSucc)) *
        (fieldIncrement h i).2) ≤ h.height (Fin.last h.depth) := by
    rw [← fieldIncrement_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_of_le_one_left (fieldIncrement_nonneg h i)
    apply field_majorant_coefficient_le_one ⟨hd.le, hd1⟩
    constructor
    · rw [← h.first]
      exact h.ordered_cut.monotone (Fin.zero_le _)
    · rw [← h.last]
      exact h.ordered_cut.monotone (Fin.le_last _)
  have he : (∑ i : Fin (h.depth + 1),
      (max (h.cut i.castSucc) d + (1 - d) * (1 - h.cut i.castSucc)) *
        (fieldIncrement h i).2) =
      2 * (∑ i : Fin (h.depth + 1),
        max (fieldIncrement h i).1 d * (fieldIncrement h i).2 / 2) +
      (1 - d) * (∑ i : Fin (h.depth + 1),
        (1 - h.cut i.castSucc) * (fieldIncrement h i).2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change _ = 2 * (max (h.cut i.castSucc) d * (fieldIncrement h i).2 / 2) + _
    ring
  rw [he] at hsum
  linarith

lemma entropyFunctional_le_of_bounded (p : OverlapPath) {d : ℝ} (hd : 0 < d)
    (hd1 : d ≤ 1) (hp : ∀ᵐ s ∂pathMeasure, p s ≤ 1 - d) :
    entropyFunctional p ≤ (((d⁻¹ - 1) * Real.log 2 : ℝ) : EReal) := by
  apply iSup_le
  intro h
  exact EReal.coe_le_coe_iff.mpr (fieldValue_add_pairing_le p hd hd1 hp h)

lemma entropyFunctional_ne_top_of_bounded (p : OverlapPath) {d : ℝ} (hd : 0 < d)
    (hd1 : d ≤ 1) (hp : ∀ᵐ s ∂pathMeasure, p s ≤ 1 - d) :
    entropyFunctional p ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (entropyFunctional_le_of_bounded p hd hd1 hp)

lemma entropyFunctional_mono {p q : OverlapPath}
    (hpq : p.val ≤ᵐ[pathMeasure] q.val) : entropyFunctional p ≤ entropyFunctional q := by
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe_iff.mpr
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply integral_mono_ae (integrable_path_mul_field p h) (integrable_path_mul_field q h)
  filter_upwards [hpq] with s hs
  exact mul_le_mul_of_nonneg_right hs (fieldFunction_nonneg h s)

end InvariantIsing

end

end OAI
