import Mathlib
import OAI.Probability.Perceptron.Interpolation.ArrayGeometry

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGibbsArray_closed_full (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    {F : Set (CompactArray CompactJointOverlap)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→NormalizedSpin (n+1)×IndexedLeaf k, sourceJointArray x ∈ F) :
    sourceGibbsArrayLaw n k f p d h u z t F=1 := by
  have hp : (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ⁻¹' F=univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) F=1
  rw [Measure.map_apply (show Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) from
      (sourceJointArray_measurable (n+1) k).comp measurable_snd) hF.measurableSet,hp]
  exact measure_univ

lemma compact_spin_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma compact_tree_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma sourceGibbsArray_limit_gram (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)) ∧
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)) := by
  constructor
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_spin_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_spin_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_spin_gram_closed r) (fun x => sourceSpinArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_tree_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_tree_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_tree_gram_closed r) (fun x => sourceTreeArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy
end

end OAI
