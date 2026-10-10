import OAI.Probability.InvariantIsing.Cavity.CavityPosteriorPair
import OAI.Probability.InvariantIsing.Fields.FieldSpinEvaluation

namespace OAI

/-! The ordinary Gaussian residual disappears from the actual spin and
common-depth test, including its exponential-integrability requirement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldVectorResidualSpinPairMean (N : ℕ) (h : FieldStep) (v : ℝ≥0) (c : ℝ)
    (z : Fin N → ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  ∫ p, referenceReplicaMean
    (((labeledLeafLaw h.depth p.1).prod (vectorGaussianLaw N v)).prod (uniformSpinPrior N))
    (fun s : (LabeledLeaf h.depth × (Fin N → ℝ)) × Spin N =>
      fieldEnergy (fieldVectorEndpoint N h p z s.1.1 + s.1.2) s.2 + (N : ℝ) * c / 2)
    (fun σ : Fin 2 → (LabeledLeaf h.depth × (Fin N → ℝ)) × Spin N =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).1.1 (σ 1).1.1))) *
        (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)))
    ∂fieldVectorCoordinateLaw N h

theorem field_vector_residual_spin_pair_reduce (N : ℕ) (hN : 0 < N)
    (h : FieldStep) (v : ℝ≥0) (c : ℝ) (z : Fin N → ℝ)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    fieldVectorResidualSpinPairMean N h v c z q Φ j =
      fieldVectorSpinPairMean N h z q Φ j := by
  unfold fieldVectorResidualSpinPairMean fieldVectorSpinPairMean
  apply integral_congr_ae
  filter_upwards [field_vector_spin_exp_integrable N hN h z] with p hp
  exact cavity_residual_spin_pair_marginal (labeledLeafLaw h.depth p.1)
    (fieldVectorEndpoint N h p z) (measurable_of_countable _) v c hp
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))) (measurable_of_countable _)

theorem field_vector_residual_spin_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    (N : ℕ) (hN : 0 < N) (h : FieldStep) (v : ℝ≥0) (c : ℝ)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ z, fieldVectorResidualSpinPairMean N h v c z q Φ j
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
      ∫ s, Φ (q (fieldLevelIndex h s)) * fieldMagnetizationPath h s ∂pathMeasure := by
  simp_rw [field_vector_residual_spin_pair_reduce N hN h v c _ q Φ j]
  exact field_vector_spin_pair_evaluation hpub N hN h q Φ j hΦ

end InvariantIsing

end

end OAI
