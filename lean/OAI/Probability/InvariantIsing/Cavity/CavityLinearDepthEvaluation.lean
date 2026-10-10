import OAI.Probability.InvariantIsing.Cavity.CavityLinearSpinEvaluation
import OAI.Probability.InvariantIsing.Fields.FieldDepthPair

namespace OAI

/-! The common-depth law of the full linear cavity model, after
projection and ordinary-residual marginalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

def cavityLabeledLinearDepthPairMean {d k : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (ψ : ℕ → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean
    (((labeledLeafLaw h.depth p.1).prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k))
    (fun x : (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      cavityLogFactor 0 L (c • 1)
        (cavityLeafSum h.depth s (labeledNoiseLeaf _ h.depth
          (p.1, markForestOfCoords _ h.depth p.2) x.1.1) + x.1.2 :
            EuclideanSpace ℝ (Fin d)) x.2)
    (fun σ : Fin 2 → (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      ψ (labeledCommonDepth h.depth (σ 0).1.1 (σ 1).1.1))
    ∂cavityLinearFieldCoordinateLaw h S

theorem cavity_labeled_linear_depth_pair_reduce {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (ψ : ℕ → ℝ) :
    cavityLabeledLinearDepthPairMean h S R L c s ψ =
      fieldVectorDepthPairMean k h (cavityProjectField L s) ψ := by
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
    _ = ∫ p, fieldDepthPairIntegrand k h (cavityProjectField L s) (f p) ψ
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
          ψ (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))
        (measurable_of_countable _)
      simpa only [fieldDepthPairIntegrand, cavityProjectField_labeled_sum,
        fieldVectorEndpoint, f] using he
    _ = _ := hp.hasLaw.integral_comp
      ((measurable_fieldDepthPairIntegrand k h ψ).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem cavity_labeled_linear_depth_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d)) (ψ : ℕ → ℝ)
    {C : ℝ} (hψ : ∀ i, |ψ i| ≤ C) :
    cavityLabeledLinearDepthPairMean h S R L c s ψ =
      ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure := by
  rw [cavity_labeled_linear_depth_pair_reduce hk h S hS R hR L v hcov hres c]
  exact field_vector_depth_pair_evaluation hpub k hk h ψ hψ _

end InvariantIsing

end

end OAI
