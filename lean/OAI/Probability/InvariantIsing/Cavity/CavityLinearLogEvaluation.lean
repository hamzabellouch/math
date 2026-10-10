import OAI.Probability.InvariantIsing.Cavity.CavityLogNormalizerTransport
import OAI.Probability.InvariantIsing.Cavity.CavityProjectedLog
import OAI.Probability.InvariantIsing.Cavity.CavityLinearNoiseEvaluation
import OAI.Probability.InvariantIsing.Fields.FieldLogMean

namespace OAI

/-! The actual rooted linear cavity log normalizer, including the
ordinary residual, is the scalar field recursion under projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

theorem cavity_linear_noise_log_ae {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ p ∂cavityLinearFieldCoordinateLaw h S,
      cavityRootedLogNormalizer h.depth 0 R L (c • 1) (uniformSpinPrior k)
        (s, labeledNoiseJoin _ h.depth (p.1, markForestOfCoords _ h.depth p.2)) =
      (k : ℝ) * (c + v) / 2 + fieldVectorLogNormalizer k h (cavityProjectField L s)
        (p.1, fun a => cavityProjectField L (p.2 a)) := by
  let f := fun p : LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d)) =>
    (p.1, fun a => cavityProjectField L (p.2 a))
  have hp : MeasurePreserving f (cavityLinearFieldCoordinateLaw h S)
      (fieldVectorCoordinateLaw k h) := by
    refine ⟨measurable_fst.prodMk (Measurable.of_eval fun a =>
      (measurable_cavityProjectField L).comp ((measurable_pi_apply a).comp measurable_snd)), ?_⟩
    exact cavity_projected_labeled_forest_law h.depth (chainExponent h.cut)
      S hS L (fieldStepVariance h) hcov
  have hgood := (cavity_linear_field_coordinates_law h S).quasiMeasurePreserving.ae
    (noiseCascade_good (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
      (chainExponent_admissible h.ordered_cut h.first h.last) (cavityGaussianMarks S))
  have hI := hp.quasiMeasurePreserving.ae
    (field_vector_spin_exp_integrable k hk h (cavityProjectField L s))
  filter_upwards [hgood, hI] with p hpGood hpI
  rw [cavityRootedLogNormalizer_eq_residual]
  have hmap := cavity_labeled_spin_prior_law h.depth p.1 p.2 hpGood
    (cavity_good_noise_total _ _ hpGood) R (uniformSpinPrior k : Measure (Spin k))
  have he := hmap.hasLaw.integral_comp
    (measurable_cavityLeafSpinPotential h.depth 0 L (c • 1) s).exp.aestronglyMeasurable
  rw [← he]
  have hfield : Integrable (fun t : Spin k × LabeledLeaf h.depth =>
      Real.exp (fieldEnergy (cavityProjectField L
        (cavityLeafSum h.depth s (labeledNoiseLeaf _ h.depth
          (p.1, markForestOfCoords _ h.depth p.2) t.2))) t.1))
      ((uniformSpinPrior k : Measure (Spin k)).prod (labeledLeafLaw h.depth p.1)) := by
    simpa only [cavityProjectField_labeled_sum, fieldVectorEndpoint, f] using hpI
  have hh := cavity_projected_log_normalizer (labeledLeafLaw h.depth p.1) R hR L v hres
    (fun α => cavityLeafSum h.depth s
      (labeledNoiseLeaf _ h.depth (p.1, markForestOfCoords _ h.depth p.2) α))
    (measurable_of_countable _) c hfield
  simpa only [Function.comp_def, cavityLabeledSpinMap, cavityProjectField_labeled_sum,
    fieldVectorEndpoint, fieldVectorLogNormalizer] using hh

theorem cavity_linear_rooted_log_integral {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (hroot : L.transpose * S₀ * L = h.height 0 • 1)
    (c : ℝ) :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
        (cavityGaussianMarks S) : Measure _)
    Integrable (cavityRootedLogNormalizer h.depth 0 R L (c • 1) (uniformSpinPrior k)) P ∧
      (∫ p, cavityRootedLogNormalizer h.depth 0 R L (c • 1) (uniformSpinPrior k) p ∂P) =
      (k : ℝ) * (c + v) / 2 +
        ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
          (fun i => vectorGaussianLaw k (fieldStepVariance h i))
          (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (y i))) z
          ∂(vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _) := by
  intro P
  let Q := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (cavityLinearFieldCoordinateLaw h S)
  let f := fun p : LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d)) =>
    (p.1, fun a => cavityProjectField L (p.2 a))
  have hf : MeasurePreserving f (cavityLinearFieldCoordinateLaw h S)
      (fieldVectorCoordinateLaw k h) := by
    refine ⟨measurable_fst.prodMk (Measurable.of_eval fun a =>
      (measurable_cavityProjectField L).comp ((measurable_pi_apply a).comp measurable_snd)), ?_⟩
    exact cavity_projected_labeled_forest_law h.depth (chainExponent h.cut)
      S hS L (fieldStepVariance h) hcov
  let A := Prod.map (cavityProjectField L) f
  have hA : MeasurePreserving A Q
      ((vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _).prod
        (fieldVectorCoordinateLaw k h)) :=
    (cavity_scalar_projected_field_law S₀ hS₀ L
      (NNReal.mk (h.height 0) (h.nonneg 0)) hroot).prod hf
  let T := Prod.map (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (fun p : LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d)) =>
      labeledNoiseJoin _ h.depth (p.1, markForestOfCoords _ h.depth p.2))
  have hT : MeasurePreserving T Q P :=
    (MeasurePreserving.id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀)).prod
      (cavity_linear_field_coordinates_law h S)
  let F := cavityRootedLogNormalizer h.depth 0 R L (c • 1) (uniformSpinPrior k)
  let G := fun p : (Fin k → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin k → ℝ)) =>
    (k : ℝ) * (c + v) / 2 + fieldVectorLogNormalizer k h p.1 p.2
  have hF : Measurable F := measurable_cavityRootedLogNormalizer _ _ _ _ _ _
  have hG : Measurable G := (measurable_fieldVectorLogNormalizer k h).const_add _
  have he : F ∘ T =ᵐ[Q] G ∘ A := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (hF.comp hT.measurable) (hG.comp hA.measurable))).mpr
    exact ae_of_all _ fun s => cavity_linear_noise_log_ae hk h S hS R hR L v hcov hres c s
  have hscalar := field_vector_log_root_integral k hk h
    (NNReal.mk (h.height 0) (h.nonneg 0))
  have hiG : Integrable G
      ((vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _).prod
        (fieldVectorCoordinateLaw k h)) := (integrable_const _).add hscalar.1
  have hi : Integrable F P := by
    rw [← hT.map_eq]
    exact (integrable_map_measure hF.aestronglyMeasurable hT.measurable.aemeasurable).mpr
      ((hA.integrable_comp_of_integrable hiG).congr he.symm)
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ p, F (T p) ∂Q := (hT.hasLaw.integral_comp hF.aestronglyMeasurable).symm
    _ = ∫ p, G (A p) ∂Q := integral_congr_ae he
    _ = ∫ p, G p ∂((vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _).prod
        (fieldVectorCoordinateLaw k h)) := hA.hasLaw.integral_comp hG.aestronglyMeasurable
    _ = _ := by
      change (∫ p, (k : ℝ) * (c + v) / 2 + fieldVectorLogNormalizer k h p.1 p.2
        ∂(vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _).prod
          (fieldVectorCoordinateLaw k h)) = _
      rw [integral_add (integrable_const _) hscalar.1, integral_const,
        probReal_univ, one_smul, hscalar.2]

end InvariantIsing

end

end OAI
