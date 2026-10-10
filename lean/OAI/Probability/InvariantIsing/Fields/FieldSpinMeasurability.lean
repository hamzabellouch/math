import OAI.Probability.InvariantIsing.Fields.FieldSpinEvaluation

namespace OAI

/-! Measurability of the actual scalar-field spin test before averaging
the Gaussian root and the labeled forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

instance fieldVectorCoordinateLaw_isProbabilityMeasure (N : ℕ) (h : FieldStep) :
    IsProbabilityMeasure (fieldVectorCoordinateLaw N h) := by
  unfold fieldVectorCoordinateLaw
  infer_instance

def fieldSpinPairIntegrand (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  referenceReplicaMean
    ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth =>
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))

lemma measurable_fieldSpinPairIntegrand (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        fieldSpinPairIntegrand N h p.1 p.2 q Φ j) := by
  let D : (Fin 2 → Spin N × LabeledLeaf h.depth) → ℝ := fun σ =>
    Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
      (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))
  have hm := measurable_cascadeCoordinateReplicaMean h.depth
    (uniformSpinPrior N : Measure (Spin N)) (measurable_fieldEnergy_map N) D
  have hc : Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        (p.1, fieldEnergyCoordinates N h p.2)) :=
    measurable_fst.prodMk ((measurable_fieldEnergyCoordinates N h).comp measurable_snd)
  have he (z : Fin N → ℝ)
      (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :
      cascadeCoordinateEnergy h.depth (fieldEnergy z) (fieldEnergyCoordinates N h p) =
        fun s => fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1 :=
    funext (fieldEnergyCoordinates_energy N h p z)
  have hh := hm.comp hc
  simp only [Function.comp_def] at hh
  simp_rw [he] at hh
  simpa only [labeledSpinReference, fieldEnergyCoordinates,
    fieldSpinPairIntegrand, D] using hh

lemma fieldSpinPairIntegrand_abs_le (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :
    |fieldSpinPairIntegrand N h z p q Φ j| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg (Φ 0)).trans (hΦ 0)
  apply referenceReplicaMean_abs_le _ _ _ (measurable_of_countable _) hC
  intro σ
  simpa only [abs_mul, abs_spinValue, mul_one, one_mul] using
    hΦ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2)))

lemma measurable_fieldVectorSpinPairMean (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    Measurable (fun z => fieldVectorSpinPairMean N h z q Φ j) :=
  (measurable_fieldSpinPairIntegrand N h q Φ j).stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
