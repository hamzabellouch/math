import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldLowerBound

namespace OAI

/-! The finite prescribed-magnetization functional has an attained bias
minimum at every interior magnetization. No optimizer or concavity premise
is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

/-- The finite canonical field value with the magnetization constraint. -/
def magneticBiasObjective (h : FieldStep) (s b : ℝ) : ℝ :=
  fieldValue h b - b * s

/-- The prescribed-magnetization field functional from (mag:constrained-functional). -/
def constrainedFieldValue (h : FieldStep) (s : ℝ) : ℝ :=
  sInf (Set.range (magneticBiasObjective h s))

lemma magneticBiasObjective_lower (h : FieldStep) (s b : ℝ) :
    (1 - |s|) * |b| - Real.log 2 - h.height (Fin.last h.depth) / 2 ≤
      magneticBiasObjective h s b := by
  have hp : b * s ≤ |b| * |s| := by
    simpa only [abs_mul] using le_abs_self (b * s)
  have hl := fieldValue_bias_lower h b
  unfold magneticBiasObjective
  nlinarith

lemma magneticBiasObjective_bddBelow (h : FieldStep) {s : ℝ} (hs : |s| ≤ 1) :
    BddBelow (Set.range (magneticBiasObjective h s)) := by
  refine ⟨-Real.log 2 - h.height (Fin.last h.depth) / 2, ?_⟩
  rintro _ ⟨b, rfl⟩
  have hp : 0 ≤ (1 - |s|) * |b| := mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg b)
  linarith [magneticBiasObjective_lower h s b]

lemma continuous_magneticBiasObjective (h : FieldStep) (s : ℝ) :
    Continuous (magneticBiasObjective h s) :=
  (continuous_fieldValue_bias h).sub (continuous_id.mul_const s)

lemma hasDerivAt_magneticBiasObjective (h : FieldStep) (s b : ℝ) :
    HasDerivAt (magneticBiasObjective h s) (fieldBiasMean h b - s) b := by
  convert (hasDerivAt_fieldValue_bias h b).sub ((hasDerivAt_id b).mul_const s) using 1
  · rfl
  · simp only [one_mul]

/-- Linear coercivity gives a genuine global optimizer, including field
profiles with tied heights or zero increments. -/
lemma exists_magneticBias_minimum (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    ∃ b : ℝ, ∀ c : ℝ, magneticBiasObjective h s b ≤ magneticBiasObjective h s c := by
  let C := Real.log 2 + h.height (Fin.last h.depth) / 2
  let δ := 1 - |s|
  let R := (C + 1) / δ
  have hδ : 0 < δ := sub_pos.mpr hs
  have hC : 0 ≤ C := add_nonneg (Real.log_nonneg (by norm_num))
    (div_nonneg (h.nonneg _) (by norm_num))
  have hR : 0 ≤ R := div_nonneg (by linarith) hδ.le
  have he : δ * R = C + 1 := by
    dsimp only [R]
    field_simp
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
    (continuous_magneticBiasObjective h s).continuousOn
  refine ⟨b, fun c => ?_⟩
  by_cases hc : c ∈ Icc (-R) R
  · exact hmin hc
  have hcr : R ≤ |c| := by
    by_contra hlt
    have hab : |c| < R := lt_of_not_ge hlt
    have hab' := abs_lt.mp hab
    exact hc ⟨hab'.1.le, hab'.2.le⟩
  have hlo := magneticBiasObjective_lower h s c
  have hlarge : 1 ≤ magneticBiasObjective h s c := by
    have hmul := mul_le_mul_of_nonneg_left hcr hδ.le
    dsimp only [δ, C] at he hmul
    linarith
  have h0 := hmin (show (0 : ℝ) ∈ Icc (-R) R by constructor <;> linarith)
  change magneticBiasObjective h s b ≤ magneticBiasObjective h s 0 at h0
  have hz : magneticBiasObjective h s 0 ≤ 0 := by
    simpa only [magneticBiasObjective, zero_mul, sub_zero] using fieldValue_nonpos h
  linarith

lemma constrainedFieldValue_eq_at_minimum (h : FieldStep) {s b : ℝ}
    (hmin : ∀ c : ℝ, magneticBiasObjective h s b ≤ magneticBiasObjective h s c) :
    constrainedFieldValue h s = magneticBiasObjective h s b := by
  apply le_antisymm
  · exact csInf_le ⟨magneticBiasObjective h s b, by rintro _ ⟨c, rfl⟩; exact hmin c⟩
      ⟨b, rfl⟩
  · exact le_csInf (range_nonempty _) (by rintro _ ⟨c, rfl⟩; exact hmin c)

lemma constrainedFieldValue_attained (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    ∃ b : ℝ, constrainedFieldValue h s = fieldValue h b - b * s ∧
      ∀ c : ℝ, fieldValue h b - b * s ≤ fieldValue h c - c * s := by
  obtain ⟨b, hb⟩ := exists_magneticBias_minimum h hs
  exact ⟨b, constrainedFieldValue_eq_at_minimum h hb, hb⟩

/-- At any minimizing bias the actual physical mean spin equals the
prescribed magnetization. -/
lemma magneticBiasMean_eq_of_minimum (h : FieldStep) {s b : ℝ}
    (hmin : ∀ c : ℝ, magneticBiasObjective h s b ≤ magneticBiasObjective h s c) :
    fieldBiasMean h b = s := by
  have hlocal : IsLocalMin (magneticBiasObjective h s) b := Eventually.of_forall hmin
  have hz := hlocal.hasDerivAt_eq_zero (hasDerivAt_magneticBiasObjective h s b)
  exact sub_eq_zero.mp hz

/-- The real minimum agrees exactly with the extended-real infimum. -/
lemma constrainedFieldValue_coe_iInf (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    (constrainedFieldValue h s : EReal) =
      ⨅ b : ℝ, ((fieldValue h b - b * s : ℝ) : EReal) := by
  obtain ⟨b, hb⟩ := exists_magneticBias_minimum h hs
  rw [constrainedFieldValue_eq_at_minimum h hb]
  apply le_antisymm
  · apply le_iInf
    intro c
    exact_mod_cast hb c
  · exact iInf_le _ b

/-- Interior minimizing biases are bounded uniformly on bounded-height
families of fields. -/
lemma magneticBias_minimum_bound (h : FieldStep) {s b C : ℝ} (hs : |s| < 1)
    (hC : h.height (Fin.last h.depth) ≤ C)
    (hmin : ∀ c : ℝ, magneticBiasObjective h s b ≤ magneticBiasObjective h s c) :
    |b| ≤ (Real.log 2 + C / 2) / (1 - |s|) := by
  have hδ : 0 < 1 - |s| := sub_pos.mpr hs
  apply (le_div_iff₀ hδ).mpr
  have hz : magneticBiasObjective h s b ≤ 0 := by
    apply (hmin 0).trans
    simpa only [magneticBiasObjective, zero_mul, sub_zero] using fieldValue_nonpos h
  have hl := magneticBiasObjective_lower h s b
  nlinarith

end InvariantIsing

end

end OAI
