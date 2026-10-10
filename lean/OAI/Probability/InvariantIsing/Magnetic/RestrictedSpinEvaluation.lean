import OAI.Probability.InvariantIsing.Magnetic.RestrictedLeafConditioning
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRootEvaluation
import OAI.Probability.InvariantIsing.Fields.FieldSpinMeasurability

namespace OAI

/-! The actual constrained spin-pair test under the finite published
endpoint marking input. Integrability is proved from the full model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedFieldSpinPairIntegrand {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  referenceReplicaMean
    ((restrictedSpinPrior S hS : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth =>
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))

def restrictedFieldSpinPairMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (z : Fin N → ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  ∫ p, restrictedFieldSpinPairIntegrand S hS h z p q Φ j ∂fieldVectorCoordinateLaw N h

lemma measurable_restrictedFieldSpinPairIntegrand {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        restrictedFieldSpinPairIntegrand S hS h p.1 p.2 q Φ j) := by
  let D : (Fin 2 → Spin N × LabeledLeaf h.depth) → ℝ := fun σ =>
    Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
      (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))
  have hm := measurable_cascadeCoordinateReplicaMean h.depth
    (restrictedSpinPrior S hS : Measure (Spin N)) (measurable_fieldEnergy_map N) D
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
    restrictedFieldSpinPairIntegrand, D] using hh

lemma restrictedFieldSpinPairIntegrand_abs_le {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :
    |restrictedFieldSpinPairIntegrand S hS h z p q Φ j| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg (Φ 0)).trans (hΦ 0)
  apply referenceReplicaMean_abs_le _ _ _ (measurable_of_countable _) hC
  intro σ
  simpa only [abs_mul, abs_spinValue, mul_one, one_mul] using
    hΦ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2)))

lemma measurable_restrictedFieldSpinPairMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    Measurable (fun z => restrictedFieldSpinPairMean S hS h z q Φ j) :=
  (measurable_restrictedFieldSpinPairIntegrand S hS h q Φ j).stronglyMeasurable.integral_prod_right'.measurable

lemma restrictedFieldSpinPairMean_abs_le {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) (z : Fin N → ℝ) :
    |restrictedFieldSpinPairMean S hS h z q Φ j| ≤ C := by
  exact abs_integral_le_const_of_bound
    ((measurable_restrictedFieldSpinPairIntegrand S hS h q Φ j).comp measurable_prodMk_left)
    (fun p => restrictedFieldSpinPairIntegrand_abs_le S hS h q Φ j hΦ z p)

theorem restricted_field_spin_pair_reduce {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (z : Fin N → ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    restrictedFieldSpinPairMean S hS h z q Φ j =
      restrictedFieldTiltedPairMean S h z (restrictedEndpointCoordinateTest S h q Φ j) := by
  unfold restrictedFieldSpinPairMean restrictedFieldSpinPairIntegrand restrictedFieldTiltedPairMean
  apply integral_congr_ae
  filter_upwards [restricted_field_vector_spin_exp_integrable hN S hS h z] with p hp
  exact restricted_leaf_spin_pair_conditioning S hS (labeledLeafLaw h.depth p.1)
    (fieldVectorEndpoint N h p z) hp (fun d => Φ (q (fieldDepthLevel h d)))
    (fun d => hΦ _) j

theorem restricted_field_spin_pair_evaluation
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ z, restrictedFieldSpinPairMean S hS h z q Φ j
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
      ∫ s, Φ (q (fieldLevelIndex h s)) *
        (∫ z, restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut)
          (fieldStepVariance h)
          (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
          (fieldLevelIndex h s) j z
          ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)))
        ∂pathMeasure := by
  simp_rw [restricted_field_spin_pair_reduce hN S hS h _ q Φ j hΦ]
  exact restricted_field_published_rooted_coordinate_test hpub hN S hS h q Φ j hΦ

end InvariantIsing

end

end OAI
