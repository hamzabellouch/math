import OAI.Probability.InvariantIsing.Cavity.CavityLinearSpinEvaluation

namespace OAI

/-! The full linear cavity exponential moment on almost every actual
independent Gaussian forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

instance cavityLinearFieldCoordinateLaw_isProbabilityMeasure {d : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (cavityLinearFieldCoordinateLaw h S) := by
  unfold cavityLinearFieldCoordinateLaw
  infer_instance

lemma cavity_linear_field_coordinates_law {d : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    MeasurePreserving
      (fun p : LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d)) =>
        labeledNoiseJoin _ h.depth (p.1, markForestOfCoords _ h.depth p.2))
      (cavityLinearFieldCoordinateLaw h S)
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
        (cavityGaussianMarks S) : Measure _) := by
  refine ⟨by fun_prop, ?_⟩
  exact labeledNoiseCoordinates_law _ h.depth (chainExponent h.cut) (cavityGaussianMarks S)

theorem cavity_linear_labeled_exp_ae {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ p ∂cavityLinearFieldCoordinateLaw h S,
      Integrable (fun x : (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
        Real.exp (cavityLogFactor 0 L (c • 1)
          (cavityLeafSum h.depth s (labeledNoiseLeaf _ h.depth
            (p.1, markForestOfCoords _ h.depth p.2) x.1.1) + x.1.2 :
              EuclideanSpace ℝ (Fin d)) x.2))
        (((labeledLeafLaw h.depth p.1).prod (multivariateGaussian 0 R)).prod
          (uniformSpinPrior k)) := by
  let f : (LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d))) →
      (LabeledTree h.depth × (ForestVertex h.depth → Fin k → ℝ)) :=
    fun p => (p.1, fun a => cavityProjectField L (p.2 a))
  have hp : MeasurePreserving f (cavityLinearFieldCoordinateLaw h S)
      (fieldVectorCoordinateLaw k h) := by
    refine ⟨measurable_fst.prodMk (Measurable.of_eval fun a =>
      (measurable_cavityProjectField L).comp ((measurable_pi_apply a).comp measurable_snd)), ?_⟩
    exact cavity_projected_labeled_forest_law h.depth (chainExponent h.cut)
      S hS L (fieldStepVariance h) hcov
  have hi := hp.quasiMeasurePreserving.ae
    (field_vector_spin_exp_integrable k hk h (cavityProjectField L s))
  filter_upwards [hi] with p hip
  let y : LabeledLeaf h.depth → EuclideanSpace ℝ (Fin d) := fun α =>
    cavityLeafSum h.depth s
      (labeledNoiseLeaf _ h.depth (p.1, markForestOfCoords _ h.depth p.2) α)
  have hy : Measurable y := measurable_of_countable _
  have hfield : Integrable (fun t : Spin k × LabeledLeaf h.depth =>
      Real.exp (fieldEnergy (cavityProjectField L (y t.2)) t.1))
      ((uniformSpinPrior k : Measure (Spin k)).prod (labeledLeafLaw h.depth p.1)) := by
    simpa only [y, cavityProjectField_labeled_sum, fieldVectorEndpoint, f] using hip
  exact cavity_projected_spin_exp_integrable (labeledLeafLaw h.depth p.1)
    R hR L v hres y hy c hfield

end InvariantIsing

end

end OAI
