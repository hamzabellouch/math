import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldMinimum

namespace OAI

/-! The bias infimum is finite and concave in the prescribed magnetization.
Its actual minimizing bias supplies the supporting slope. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma constrainedFieldValue_le_trial (h : FieldStep) {s : ℝ} (hs : |s| ≤ 1) (b : ℝ) :
    constrainedFieldValue h s ≤ fieldValue h b - b * s :=
  csInf_le (magneticBiasObjective_bddBelow h hs) ⟨b, rfl⟩

lemma constrainedFieldValue_bounds (h : FieldStep) {s : ℝ} (hs : |s| ≤ 1) :
    -Real.log 2 - h.height (Fin.last h.depth) / 2 ≤ constrainedFieldValue h s ∧
      constrainedFieldValue h s ≤ 0 := by
  constructor
  · apply le_csInf (range_nonempty _)
    rintro _ ⟨b, rfl⟩
    have hp : 0 ≤ (1 - |s|) * |b| := mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg b)
    linarith [magneticBiasObjective_lower h s b]
  · have h0 := constrainedFieldValue_le_trial h hs 0
    simp only [zero_mul, sub_zero] at h0
    exact h0.trans (fieldValue_nonpos h)

lemma concaveOn_constrainedFieldValue_magnetization (h : FieldStep) :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (constrainedFieldValue h) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro s hs t ht a b ha hb hab
  have hs' : |s| ≤ 1 := abs_le.mpr hs
  have ht' : |t| ≤ 1 := abs_le.mpr ht
  apply le_csInf (range_nonempty _)
  rintro _ ⟨c, rfl⟩
  have hsc := mul_le_mul_of_nonneg_left (constrainedFieldValue_le_trial h hs' c) ha
  have htc := mul_le_mul_of_nonneg_left (constrainedFieldValue_le_trial h ht' c) hb
  simp only [smul_eq_mul, magneticBiasObjective]
  calc
    a * constrainedFieldValue h s + b * constrainedFieldValue h t ≤
        a * (fieldValue h c - c * s) + b * (fieldValue h c - c * t) := add_le_add hsc htc
    _ = (a + b) * fieldValue h c - c * (a * s + b * t) := by ring
    _ = fieldValue h c - c * (a * s + b * t) := by rw [hab, one_mul]

lemma constrainedFieldValue_bias_support (h : FieldStep) {s t b : ℝ}
    (ht : |t| ≤ 1)
    (hmin : ∀ c, magneticBiasObjective h s b ≤ magneticBiasObjective h s c) :
    constrainedFieldValue h t ≤ constrainedFieldValue h s - b * (t - s) := by
  rw [constrainedFieldValue_eq_at_minimum h hmin]
  have h := constrainedFieldValue_le_trial h ht b
  unfold magneticBiasObjective
  linarith

/-- An explicit local Lipschitz bound uniform over all field partitions
whose total height is bounded. -/
lemma constrainedFieldValue_magnetization_lipschitz (h : FieldStep)
    {s t r C : ℝ} (hr : r < 1) (hs : |s| ≤ r) (ht : |t| ≤ r)
    (hC : h.height (Fin.last h.depth) ≤ C) :
    |constrainedFieldValue h s - constrainedFieldValue h t| ≤
      ((Real.log 2 + C / 2) / (1 - r)) * |s - t| := by
  obtain ⟨b, hb⟩ := exists_magneticBias_minimum h (hs.trans_lt hr)
  obtain ⟨c, hc⟩ := exists_magneticBias_minimum h (ht.trans_lt hr)
  have hδ : 0 < 1 - r := sub_pos.mpr hr
  have hM : 0 ≤ Real.log 2 + C / 2 := by
    have hc0 := (h.nonneg (Fin.last h.depth)).trans hC
    positivity
  have hbb := magneticBias_minimum_bound h (hs.trans_lt hr) hC hb
  have hcc := magneticBias_minimum_bound h (ht.trans_lt hr) hC hc
  have hbs : |b| ≤ (Real.log 2 + C / 2) / (1 - r) := hbb.trans
    (div_le_div_of_nonneg_left hM hδ (by linarith))
  have hct : |c| ≤ (Real.log 2 + C / 2) / (1 - r) := hcc.trans
    (div_le_div_of_nonneg_left hM hδ (by linarith))
  have hst := constrainedFieldValue_bias_support h (ht.trans hr.le) hb
  have hts := constrainedFieldValue_bias_support h (hs.trans hr.le) hc
  rw [abs_le]
  constructor
  · have hp : -(b * (t - s)) ≤
        ((Real.log 2 + C / 2) / (1 - r)) * |s - t| := by
      calc
        _ ≤ |b * (t - s)| := neg_le_abs _
        _ = |b| * |s - t| := by rw [abs_mul, abs_sub_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_right hbs (abs_nonneg _)
    linarith
  · have hp : -c * (s - t) ≤
        ((Real.log 2 + C / 2) / (1 - r)) * |s - t| := by
      calc
        _ ≤ |-c * (s - t)| := le_abs_self _
        _ = |c| * |s - t| := by rw [abs_mul, abs_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_right hct (abs_nonneg _)
    linarith

end InvariantIsing

end

end OAI
