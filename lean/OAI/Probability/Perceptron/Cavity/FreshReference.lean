import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshThermalLaw
import OAI.Probability.Perceptron.Cavity.LeafFreshLog

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceFreshReferenceData (n k : ℕ) (p : Fin (n+1)→ℕ) :=
  (EuclideanSpace ℝ (Fin 1)×EnrichedMark (n+1) (n+1) p)×
    (IndexedCascadeBase k×(IndexedCascadeMarks (EuclideanSpace ℝ (Fin 1)) k×
      IndexedCascadeMarks (EnrichedMark (n+1) (n+1) p) k))

def sourceFreshReferenceLog (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (A : ℕ→EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (R : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (F : EuclideanSpace ℝ (Fin 1)→ℝ) (v : SourceFreshReferenceData n k p) : ℝ :=
  Real.log (tiltMean (indexedLeafProbability k v.2.1)
    (fun l => enrichedTerminal n M f a p u (h (Fin.last k))
      (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
        ((fun _ => enrichedRootMap p d h v.1.2),v.2.2.2) l 0))
    (fun l => Real.exp (F (indexedLeafState (gaussianLinearMarkStep A) k
      ((fun _ => R v.1.1),v.2.2.1) l 0))) 1)

lemma sourceFreshReferenceLog_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (A : ℕ→EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (R : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    {F : EuclideanSpace ℝ (Fin 1)→ℝ} (hF : Measurable F) :
    Measurable (sourceFreshReferenceLog n M k f a p d h u A R F) := by
  let κ : Kernel (SourceFreshReferenceData n k p) (IndexedLeaf k) :=
    (indexedLeafKernel k).comap (fun v => v.2.1) measurable_snd.fst
  have hs₁ : Measurable (fun t : SourceFreshReferenceData n k p×IndexedLeaf k =>
      indexedLeafState (gaussianLinearMarkStep A) k
        ((fun _ => R t.1.1.1),t.1.2.2.1) t.2) :=
    (indexedLeafState_measurable (gaussianLinearMarkStep_measurable A) k).comp
      (show Measurable (fun t : SourceFreshReferenceData n k p×IndexedLeaf k =>
        (((fun _ => R t.1.1.1),t.1.2.2.1),t.2)) from by fun_prop)
  have hs₂ : Measurable (fun t : SourceFreshReferenceData n k p×IndexedLeaf k =>
      indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
        ((fun _ => enrichedRootMap p d h t.1.1.2),t.1.2.2.2) t.2) :=
    (indexedLeafState_measurable
      (gaussianLinearMarkStep_measurable (enrichedIncrementMap p d h)) k).comp
      (show Measurable (fun t : SourceFreshReferenceData n k p×IndexedLeaf k =>
        (((fun _ => enrichedRootMap p d h t.1.1.2),t.1.2.2.2),t.2)) from by fun_prop)
  exact (kernel_tiltMean_measurable κ
    (H := fun v l => enrichedTerminal n M f a p u (h (Fin.last k))
      (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
        ((fun _ => enrichedRootMap p d h v.1.2),v.2.2.2) l 0))
    (Y := fun v l => Real.exp (F (indexedLeafState (gaussianLinearMarkStep A) k
      ((fun _ => R v.1.1),v.2.2.1) l 0)))
    ((enrichedTerminal_lipschitz n M f a p u (h (Fin.last k))).continuous.measurable.comp
      ((measurable_pi_apply 0).comp hs₂))
    (hF.comp ((measurable_pi_apply 0).comp hs₁) |>.exp)).log

lemma sourceFreshReferenceLog_bound (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (A : ℕ→EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (R : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    {F : EuclideanSpace ℝ (Fin 1)→ℝ} {C : ℝ} (hC : 0≤C) (hFC : ∀ x, |F x|≤C)
    (v : SourceFreshReferenceData n k p) :
    |sourceFreshReferenceLog n M k f a p d h u A R F v|≤C := by
  exact log_tiltMean_exp_bound_general _ (measurable_of_countable _)
    (measurable_of_countable _) hC (fun _ => hFC _)

theorem source_countable_fresh_reference_value (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (A : ℕ→EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (R : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    {F : EuclideanSpace ℝ (Fin 1)→ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    {C : ℝ} (hC : 0≤C) (hFC : ∀ x, |F x|≤C) :
    (∫ t : IndexedCascadeBase k×((ℕ→ℝ)×(ℕ→ℝ)),
      sourceFreshReferenceLog n M k f a p d h u A R F
        (((indexedGaussianDisorder k (Fin 1) t.2.1).1,
          (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) t.2.2).1),
         (t.1,((indexedGaussianDisorder k (Fin 1) t.2.1).2,
          (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) t.2.2).2)))
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (countableGaussianLaw.prod countableGaussianLaw)) =
      ∫ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
        (linearCascadeWord A k z) F (R x) ∂stdGaussian (EuclideanSpace ℝ (Fin 1)) := by
  have hm := sourceFreshReferenceLog_measurable n M k f a p d h u A R hF.continuous.measurable
  have hp := indexedGaussian_fresh_regroup_law k z (Fin 1) (EnrichedIndex (n+1) (n+1) p)
  have he := integral_map
    (μ := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
      (countableGaussianLaw.prod countableGaussianLaw))
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  rw [← he]
  have hi : Integrable (sourceFreshReferenceLog n M k f a p d h u A R F)
      (((stdGaussian (EuclideanSpace ℝ (Fin 1))).prod
        (stdGaussian (EnrichedMark (n+1) (n+1) p))).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          ((indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ (Fin 1))) k :
            Measure (IndexedCascadeMarks (EuclideanSpace ℝ (Fin 1)) k)).prod
            (indexedCascadeMarksLaw (gaussianMarkLaw (E := EnrichedMark (n+1) (n+1) p)) k)))) := by
    apply Integrable.of_bound hm.aestronglyMeasurable C
    exact ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs] using sourceFreshReferenceLog_bound n M k f a p d h u A R hC hFC v
  rw [integral_prod _ hi]
  exact source_leaf_independent_fresh_log_roots n M k f a p d h u z hz hz0 hz1 A R hF

end SphericalPerceptronFreeEnergy
end

end OAI
