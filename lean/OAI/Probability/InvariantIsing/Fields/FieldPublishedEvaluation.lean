import OAI.Probability.InvariantIsing.Fields.FieldPublishedPairInput

namespace OAI

/-! Evaluating the finite published endpoint law on physical spin means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldDepthLevel (h : FieldStep) (d : ℕ) : Fin (h.depth + 1) :=
  ⟨min d h.depth, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma fieldDepthLevel_common (h : FieldStep) (α : ℕ → LabeledLeaf h.depth) :
    fieldDepthLevel h (labeledCommonDepth h.depth (α 0) (α 1)) = fieldCommonLevel h α := by
  apply Fin.ext
  exact min_eq_left (labeledCommonDepth_le _ _ _)

def fieldEndpointCoordinateTest (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    (p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ))) : ℝ :=
  Φ (q (fieldDepthLevel h p.1)) * (Real.tanh (p.2.1 j) * Real.tanh (p.2.2 j))

lemma measurable_fieldEndpointCoordinateTest (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    Measurable (fieldEndpointCoordinateTest N h q Φ j) := by
  exact ((measurable_of_countable (fun d => Φ (q (fieldDepthLevel h d)))).comp
    measurable_fst).mul
    ((field_tanh_measurable.comp ((measurable_pi_apply j).comp measurable_snd.fst)).mul
      (field_tanh_measurable.comp ((measurable_pi_apply j).comp measurable_snd.snd)))

lemma fieldEndpointCoordinateTest_bound (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C)
    (p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ))) :
    |fieldEndpointCoordinateTest N h q Φ j p| ≤ C := by
  unfold fieldEndpointCoordinateTest
  rw [abs_mul, abs_mul]
  calc
    _ ≤ C * (1 * 1) := mul_le_mul (hΦ _) (mul_le_mul
      (field_abs_tanh_le_one _) (field_abs_tanh_le_one _) (abs_nonneg _) zero_le_one)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((abs_nonneg (Φ 0)).trans (hΦ 0))
    _ = C := by ring

theorem field_published_coordinate_test (hpub : PanchenkoTalagrandFieldPairInput)
    (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) (z : Fin N → ℝ) :
    fieldVectorTiltedPairMean N h z (fieldEndpointCoordinateTest N h q Φ j) =
      ∫ α : ℕ → LabeledLeaf h.depth,
        Φ (q (fieldCommonLevel h α)) *
          fieldScalarSquares (scalarFieldIncrements h)
            (fun u => Real.log (Real.cosh u)) Real.tanh
            (Fin.cast (by rw [scalarFieldIncrements_length]) (fieldCommonLevel h α)) (z j)
        ∂cascadeReplicaLaw h.depth (chainExponent h.cut) := by
  rw [hpub N hN h z _ (measurable_fieldEndpointCoordinateTest N h q Φ j)
    ⟨C, fieldEndpointCoordinateTest_bound N h q Φ j hΦ⟩]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  simp only [fieldEndpointCoordinateTest]
  have hc : fieldDepthLevel h (fieldCommonLevel h α).val = fieldCommonLevel h α := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ (fieldCommonLevel h α).isLt)
  rw [hc, integral_const_mul, fieldVectorPairEndpointKernel_coordinate_mean]

lemma field_root_average_squares (N : ℕ) (h : FieldStep)
    (i : Fin (h.depth + 1)) (j : Fin N) :
    (∫ z : Fin N → ℝ, fieldScalarSquares (scalarFieldIncrements h)
      (fun u => Real.log (Real.cosh u)) Real.tanh
      (Fin.cast (by rw [scalarFieldIncrements_length]) i) (z j)
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
        fieldMagnetizationLevel h i := by
  have hs := fieldScalarSquares_regular (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h) measurable_logCosh logCosh_linearGrowth
    field_tanh_measurable field_abs_tanh_le_one
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
  change (∫ z : Fin N → ℝ, _
    ∂Measure.pi (fun _ : Fin N => gaussianReal 0 (NNReal.mk (h.height 0) (h.nonneg 0)))) = _
  rw [integral_comp_eval hs.1.aestronglyMeasurable]
  rfl

lemma measurable_fieldCommonLevel (h : FieldStep) : Measurable (fieldCommonLevel h) := by
  have hm : Measurable (fun p : LabeledLeaf h.depth × LabeledLeaf h.depth =>
      (⟨labeledCommonDepth h.depth p.1 p.2,
        Nat.lt_succ_of_le (labeledCommonDepth_le _ _ _)⟩ : Fin (h.depth + 1))) :=
    measurable_of_countable _
  have hp : Measurable (fun α : ℕ → LabeledLeaf h.depth => (α 0, α 1)) := by fun_prop
  exact hm.comp hp

theorem field_published_rooted_coordinate_test (hpub : PanchenkoTalagrandFieldPairInput)
    (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ z, fieldVectorTiltedPairMean N h z (fieldEndpointCoordinateTest N h q Φ j)
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
      ∫ s, Φ (q (fieldLevelIndex h s)) * fieldMagnetizationPath h s ∂pathMeasure := by
  let μ : Measure (Fin N → ℝ) := vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0))
  let ν := cascadeReplicaLaw h.depth (chainExponent h.cut)
  let a : Fin (h.depth + 1) → (Fin N → ℝ) → ℝ := fun i z =>
    Φ (q i) * fieldScalarSquares (scalarFieldIncrements h)
      (fun u => Real.log (Real.cosh u)) Real.tanh
      (Fin.cast (by rw [scalarFieldIncrements_length]) i) (z j)
  have ha (i : Fin (h.depth + 1)) : Measurable (a i) := by
    have hs := fieldScalarSquares_regular (scalarFieldIncrements h)
      (scalarFieldIncrements_positive h) measurable_logCosh logCosh_linearGrowth
      field_tanh_measurable field_abs_tanh_le_one
      (Fin.cast (by rw [scalarFieldIncrements_length]) i)
    exact (hs.1.comp (measurable_pi_apply j)).const_mul _
  have ham' : Measurable (fun p : Fin (h.depth + 1) × (Fin N → ℝ) => a p.1 p.2) :=
    measurable_from_prod_countable_right ha
  have hp : Measurable (fun p : (Fin N → ℝ) × (ℕ → LabeledLeaf h.depth) =>
      (fieldCommonLevel h p.2, p.1)) :=
    ((measurable_fieldCommonLevel h).comp measurable_snd).prodMk measurable_fst
  have ham : Measurable (fun p : (Fin N → ℝ) × (ℕ → LabeledLeaf h.depth) =>
      a (fieldCommonLevel h p.2) p.1) := ham'.comp hp
  have hai : Integrable (fun p : (Fin N → ℝ) × (ℕ → LabeledLeaf h.depth) =>
      a (fieldCommonLevel h p.2) p.1) (μ.prod ν) := by
    apply Integrable.of_bound ham.aestronglyMeasurable C
    apply ae_of_all
    intro p
    have hs := (fieldScalarSquares_regular (scalarFieldIncrements h)
      (scalarFieldIncrements_positive h) measurable_logCosh logCosh_linearGrowth
      field_tanh_measurable field_abs_tanh_le_one
      (Fin.cast (by rw [scalarFieldIncrements_length]) (fieldCommonLevel h p.2))).2 (p.1 j)
    change ‖Φ (q (fieldCommonLevel h p.2)) * _‖ ≤ C
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg _)).trans (by simpa using hΦ _)
  simp_rw [field_published_coordinate_test hpub N hN h q Φ j hΦ]
  change (∫ z, ∫ α, a (fieldCommonLevel h α) z ∂ν ∂μ) = _
  rw [integral_integral_swap hai]
  have hi (i : Fin (h.depth + 1)) : (∫ z, a i z ∂μ) = Φ (q i) * fieldMagnetizationLevel h i := by
    rw [show a i = (fun z => Φ (q i) * fieldScalarSquares (scalarFieldIncrements h)
      (fun u => Real.log (Real.cosh u)) Real.tanh
      (Fin.cast (by rw [scalarFieldIncrements_length]) i) (z j)) from rfl,
      integral_const_mul, field_root_average_squares]
  simp_rw [hi]
  exact fieldCommonLevel_integral h (fun i => Φ (q i) * fieldMagnetizationLevel h i)

end InvariantIsing

end

end OAI
