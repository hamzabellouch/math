import OAI.Probability.InvariantIsing.Cavity.CavityProjectedPair
import OAI.Probability.InvariantIsing.Fields.FieldSpinMeasurability

namespace OAI

/-! Evaluation of the full linear cavity spin test under its independent
Euclidean Gaussian forest and root. The covariance assumptions specify
the scalar field path after projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

def cavityLinearFieldCoordinateLaw {d : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    Measure (LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d))) :=
  (labeledCascadeLaw h.depth (chainExponent h.cut) : Measure (LabeledTree h.depth)).prod
    (Measure.infinitePi (fun a : ForestVertex h.depth =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth h.depth a))))

def cavityLabeledLinearSpinPairMean {d k : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin k) : ℝ :=
  ∫ p, referenceReplicaMean
    (((labeledLeafLaw h.depth p.1).prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k))
    (fun x : (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      cavityLogFactor 0 L (c • 1)
        (cavityLeafSum h.depth s (labeledNoiseLeaf _ h.depth
          (p.1, markForestOfCoords _ h.depth p.2) x.1.1) + x.1.2 :
            EuclideanSpace ℝ (Fin d)) x.2)
    (fun σ : Fin 2 → (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).1.1 (σ 1).1.1))) *
        (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)))
    ∂cavityLinearFieldCoordinateLaw h S

theorem cavity_labeled_linear_spin_pair_reduce {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin k) :
    cavityLabeledLinearSpinPairMean h S R L c s q Φ j =
      fieldVectorSpinPairMean k h (cavityProjectField L s) q Φ j := by
  let f : (LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d))) →
      (LabeledTree h.depth × (ForestVertex h.depth → Fin k → ℝ)) :=
    fun p => (p.1, fun a => cavityProjectField L (p.2 a))
  have hf : Measurable f := measurable_fst.prodMk (Measurable.of_eval fun a =>
    (measurable_cavityProjectField L).comp ((measurable_pi_apply a).comp measurable_snd))
  have hp : MeasurePreserving f (cavityLinearFieldCoordinateLaw h S)
      (fieldVectorCoordinateLaw k h) :=
    ⟨hf, cavity_projected_labeled_forest_law h.depth (chainExponent h.cut)
      S hS L (fieldStepVariance h) hcov⟩
  have hi := hp.quasiMeasurePreserving.ae
    (field_vector_spin_exp_integrable k hk h (cavityProjectField L s))
  calc
    _ = ∫ p, fieldSpinPairIntegrand k h (cavityProjectField L s) (f p) q Φ j
        ∂cavityLinearFieldCoordinateLaw h S := by
      apply integral_congr_ae
      filter_upwards [hi] with p hip
      have he := cavity_projected_spin_pair_reduce (labeledLeafLaw h.depth p.1)
        R hR L v hres
        (fun α => cavityLeafSum h.depth s
          (labeledNoiseLeaf _ h.depth (p.1, markForestOfCoords _ h.depth p.2) α))
        (measurable_of_countable _) c
        (by simpa only [cavityProjectField_labeled_sum, fieldVectorEndpoint, f] using hip)
        (fun σ : Fin 2 → Spin k × LabeledLeaf h.depth =>
          Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
            (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))
        (measurable_of_countable _)
      simpa only [fieldSpinPairIntegrand, cavityProjectField_labeled_sum,
        fieldVectorEndpoint, f] using he
    _ = _ := hp.hasLaw.integral_comp
      ((measurable_fieldSpinPairIntegrand k h q Φ j).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem cavity_labeled_linear_spin_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (hroot : L.transpose * S₀ * L = h.height 0 • 1)
    (c : ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin k)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ s, cavityLabeledLinearSpinPairMean h S R L c s q Φ j
      ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀) =
      ∫ t, Φ (q (fieldLevelIndex h t)) * fieldMagnetizationPath h t ∂pathMeasure := by
  simp_rw [cavity_labeled_linear_spin_pair_reduce hk h S hS R hR L v hcov hres c]
  have hp := cavity_scalar_projected_field_law S₀ hS₀ L
    (NNReal.mk (h.height 0) (h.nonneg 0)) hroot
  have hi := hp.hasLaw.integral_comp
    (measurable_fieldVectorSpinPairMean k h q Φ j).aestronglyMeasurable
  simp only [Function.comp_def] at hi
  exact hi.trans (field_vector_spin_pair_evaluation hpub k hk h q Φ j hΦ)

end InvariantIsing

end

end OAI
