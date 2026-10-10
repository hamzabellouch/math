import OAI.Probability.InvariantIsing.Cavity.CavityLinearNoiseEvaluation
import OAI.Probability.InvariantIsing.Magnetic.RestrictedLinearDepthEvaluation
import OAI.Probability.InvariantIsing.Fields.PriorLabeledDepthPair
import OAI.Probability.InvariantIsing.Fields.PriorLinearIntegrability
import OAI.Probability.InvariantIsing.Cavity.CavityRootedDepthMean

namespace OAI

/-! Preservation of common-depth law under the full linear rooted Gibbs tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal ENNReal

namespace InvariantIsing

theorem restricted_cavity_linear_noise_depth_test {d k : ℕ} (hk : 0 < k) (T : Finset (Spin k)) (hT : T.Nonempty) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (hAtom : ∀ i < h.depth,
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)))
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (ψ : ℕ → ℝ) :
    (∫ V, cavityRootedDepthTestMean h.depth 0 R L (c • 1) (restrictedSpinPrior T hT)
      ψ (s, V)
      ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
        (cavityGaussianMarks S) : Measure _)) =
      restrictedCavityLinearDepthPairMean T hT h S R L c s ψ := by
  let f := fun p : LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d)) =>
    labeledNoiseJoin _ h.depth (p.1, markForestOfCoords _ h.depth p.2)
  have hp := cavity_linear_field_coordinates_law h S
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  have hgood := hp.quasiMeasurePreserving.ae
    (noiseCascade_good (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut) hb
      (cavityGaussianMarks S))
  have hgi : ∀ᵐ p ∂cavityLinearFieldCoordinateLaw h S, Function.Injective p.2 :=
    (measurePreserving_snd
      (μ := (labeledCascadeLaw h.depth (chainExponent h.cut) : Measure (LabeledTree h.depth)))
      (ν := Measure.infinitePi (fun a : ForestVertex h.depth =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth h.depth a))))).quasiMeasurePreserving.ae
      (cavity_atomless_marks_injective h.depth (cavityGaussianMarks S) hAtom)
  have hI := prior_cavity_linear_labeled_exp_ae hk (restrictedSpinPrior T hT) h S hS R hR L v hcov hres c s
  have hm : Measurable (fun V => cavityRootedDepthTestMean h.depth 0 R L (c • 1)
      (restrictedSpinPrior T hT) ψ (s, V)) :=
    (measurable_cavityRootedDepthTestMean h.depth 0 R L (c • 1) (restrictedSpinPrior T hT)
      ψ).comp (measurable_const.prodMk measurable_id)
  calc
    _ = ∫ p, cavityRootedDepthTestMean h.depth 0 R L (c • 1) (restrictedSpinPrior T hT)
        ψ (s, f p)
        ∂cavityLinearFieldCoordinateLaw h S :=
      (hp.hasLaw.integral_comp hm.aestronglyMeasurable).symm
    _ = _ := by
      unfold restrictedCavityLinearDepthPairMean
      apply integral_congr_ae
      filter_upwards [hgood, hgi, hI] with p hpGood hpGi hpI
      exact prior_cavity_labeled_rooted_depth_pair h.depth 0 R L (c • 1) (restrictedSpinPrior T hT) s p.1 p.2 hpGi hpGood
        (cavity_good_noise_total _ _ hpGood) hpI ψ

theorem restricted_cavity_linear_rooted_depth_evaluation (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {d k : ℕ} (hk : 0 < k) (T : Finset (Spin k)) (hT : T.Nonempty) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (hAtom : ∀ i < h.depth,
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)))
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d)) (ψ : ℕ → ℝ)
    {C : ℝ} (hψ : ∀ i, |ψ i| ≤ C) :
    (∫ V, cavityRootedDepthTestMean h.depth 0 R L (c • 1) (restrictedSpinPrior T hT) ψ (s,V)
      ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
        (cavityGaussianMarks S) : Measure _)) =
      ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure := by
  rw [restricted_cavity_linear_noise_depth_test hk T hT h S hS hAtom R hR L v hcov hres c]
  exact restricted_cavity_labeled_linear_depth_pair_evaluation hpub hk T hT h S hS R hR L v hcov hres c s ψ hψ

end InvariantIsing

end

end OAI
