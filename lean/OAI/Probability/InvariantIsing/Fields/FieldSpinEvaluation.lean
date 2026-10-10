import OAI.Probability.InvariantIsing.Fields.FieldEnergyCoordinates
import OAI.Probability.InvariantIsing.Fields.FieldSpinPairConditioning

namespace OAI

/-! The actual finite vector-spin common-depth test under the published
marking input. Both the spin conditioning and exponential integrability
are derived for this model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def fieldVectorSpinPairMean (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  ∫ p, referenceReplicaMean
    ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth =>
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))
    ∂fieldVectorCoordinateLaw N h

theorem field_vector_spin_pair_reduce (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (z : Fin N → ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    fieldVectorSpinPairMean N h z q Φ j =
      fieldVectorTiltedPairMean N h z (fieldEndpointCoordinateTest N h q Φ j) := by
  unfold fieldVectorSpinPairMean fieldVectorTiltedPairMean
  apply integral_congr_ae
  filter_upwards [field_vector_spin_exp_integrable N hN h z] with p hp
  exact field_leaf_spin_pair_conditioning (labeledLeafLaw h.depth p.1)
    (fieldVectorEndpoint N h p z) hp (fun d => Φ (q (fieldDepthLevel h d)))
    (fun d => hΦ _) j

/-- The finite-cascade identity `cav:spin-test`, for the scalar field
representation, conditional only on the published endpoint marking law. -/
theorem field_vector_spin_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ z, fieldVectorSpinPairMean N h z q Φ j
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
      ∫ s, Φ (q (fieldLevelIndex h s)) * fieldMagnetizationPath h s ∂pathMeasure := by
  simp_rw [field_vector_spin_pair_reduce N hN h _ q Φ j hΦ]
  exact field_published_rooted_coordinate_test hpub N hN h q Φ j hΦ

end InvariantIsing

end

end OAI
