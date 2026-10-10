import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedMarkProduct

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

theorem source_leaf_independent_fresh_log
    (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (A : ℕ→EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    {F : EuclideanSpace ℝ (Fin 1)→ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (x : EuclideanSpace ℝ (Fin 1)) (y : EnrichedMark (n+1) (n+1) p) :
    (∫ b, Real.log (tiltMean (indexedLeafProbability k b.1)
      (fun l => enrichedTerminal n M f a p u (h (Fin.last k))
        (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
          ((fun _ => y),b.2.2) l 0))
      (fun l => Real.exp (F (indexedLeafState (gaussianLinearMarkStep A) k
        ((fun _ => x),b.2.1) l 0))) 1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ (Fin 1))) k :
          Measure (IndexedCascadeMarks (EuclideanSpace ℝ (Fin 1)) k)).prod
          (indexedCascadeMarksLaw (gaussianMarkLaw (E := EnrichedMark (n+1) (n+1) p)) k))) =
      gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
        (linearCascadeWord A k z) F x := by
  let : IsGaussian (gaussianMarkLaw (E := EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  let : IsGaussian (gaussianMarkLaw (E := EnrichedMark (n+1) (n+1) p) : Measure (EnrichedMark (n+1) (n+1) p)) :=
    (inferInstance : IsGaussian (stdGaussian (EnrichedMark (n+1) (n+1) p)))
  have hG := enrichedTerminal_lipschitz n M f a p u (h (Fin.last k))
  have hIF := gaussianLinearRecursion_realization
    (gaussianMarkLaw (E := EuclideanSpace ℝ (Fin 1))) A hF k z hz0
  have hIG := gaussianLinearRecursion_realization
    (gaussianMarkLaw (E := EnrichedMark (n+1) (n+1) p))
    (enrichedIncrementMap p d h) hG k z hz0
  exact (indexed_independent_arrays_fresh_log
    (gaussianMarkLaw (E := EuclideanSpace ℝ (Fin 1)))
    (gaussianMarkLaw (E := EnrichedMark (n+1) (n+1) p))
    (gaussianLinearMarkStep A) (gaussianLinearMarkStep (enrichedIncrementMap p d h))
    (gaussianLinearMarkStep_measurable A)
    (gaussianLinearMarkStep_measurable (enrichedIncrementMap p d h))
    k z hz hz0 hz1
    (hF.continuous.measurable.comp (measurable_pi_apply 0))
    (hG.continuous.measurable.comp (measurable_pi_apply 0))
    hIF.2 hIG.2 (fun _ => x) (fun _ => y)).trans (hIF.1 (fun _ => x))

theorem source_leaf_independent_fresh_log_roots
    (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (A : ℕ→EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (R : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    {F : EuclideanSpace ℝ (Fin 1)→ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    (∫ r, (∫ b, Real.log (tiltMean (indexedLeafProbability k b.1)
      (fun l => enrichedTerminal n M f a p u (h (Fin.last k))
        (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
          ((fun _ => enrichedRootMap p d h r.2),b.2.2) l 0))
      (fun l => Real.exp (F (indexedLeafState (gaussianLinearMarkStep A) k
        ((fun _ => R r.1),b.2.1) l 0))) 1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ (Fin 1))) k :
          Measure (IndexedCascadeMarks (EuclideanSpace ℝ (Fin 1)) k)).prod
          (indexedCascadeMarksLaw (gaussianMarkLaw (E := EnrichedMark (n+1) (n+1) p)) k)))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin 1))).prod
        (stdGaussian (EnrichedMark (n+1) (n+1) p))) =
      ∫ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
        (linearCascadeWord A k z) F (R x) ∂stdGaussian (EuclideanSpace ℝ (Fin 1)) := by
  simp_rw [source_leaf_independent_fresh_log n M k f a p d h u z hz hz0 hz1 A hF]
  simpa only [probReal_univ,one_smul] using
    (integral_fun_fst (μ := stdGaussian (EuclideanSpace ℝ (Fin 1)))
      (ν := stdGaussian (EnrichedMark (n+1) (n+1) p))
      (fun x => gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
        (linearCascadeWord A k z) F (R x)))

lemma freshRoot_swap_nested {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun t : A×(B×C) => (t.2.1,(t.1,t.2.2)))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  have h₁ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ν ρ)
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
    (MeasurePreserving.id ρ)
  exact (measurePreserving_prodAssoc ν μ ρ).comp (h₂.comp h₁)

lemma freshRoot_four_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ] :
    MeasurePreserving (fun t : (A×B)×(C×D) => ((t.1.1,t.2.1),(t.1.2,t.2.2)))
      ((μ.prod ν).prod (ρ.prod σ)) ((μ.prod ρ).prod (ν.prod σ)) := by
  have h₁ := measurePreserving_prodAssoc μ ν (ρ.prod σ)
  have h₂ := (MeasurePreserving.id μ).prod (freshRoot_swap_nested ν ρ σ)
  have h₃ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ρ (ν.prod σ))
  exact h₃.comp (h₂.comp h₁)

lemma freshRoot_five_regroup {B X S Y T : Type*}
    [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace Y] [MeasurableSpace T]
    (β : Measure B) (μ : Measure X) (ν : Measure S) (ρ : Measure Y) (σ : Measure T)
    [SFinite β] [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ] :
    MeasurePreserving
      (fun t : B×((X×S)×(Y×T)) => ((t.2.1.1,t.2.2.1),(t.1,(t.2.1.2,t.2.2.2))))
      (β.prod ((μ.prod ν).prod (ρ.prod σ))) ((μ.prod ρ).prod (β.prod (ν.prod σ))) := by
  exact (freshRoot_swap_nested β (μ.prod ρ) (ν.prod σ)).comp
    ((MeasurePreserving.id β).prod (freshRoot_four_shuffle μ ν ρ σ))

lemma indexedGaussian_fresh_regroup_law (k : ℕ) (z : Fin k→ℝ)
    (I J : Type) [Fintype I] [Fintype J] :
    MeasurePreserving
      (fun t : IndexedCascadeBase k×((ℕ→ℝ)×(ℕ→ℝ)) =>
        (((indexedGaussianDisorder k I t.2.1).1,(indexedGaussianDisorder k J t.2.2).1),
         (t.1,((indexedGaussianDisorder k I t.2.1).2,(indexedGaussianDisorder k J t.2.2).2))))
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (countableGaussianLaw.prod countableGaussianLaw))
      (((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          ((indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ I)) k :
            Measure (IndexedCascadeMarks (EuclideanSpace ℝ I) k)).prod
            (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ J)) k)))) := by
  have hI : MeasurePreserving (indexedGaussianDisorder k I) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ I)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ I)) k)) :=
    ⟨indexedGaussianDisorder_measurable k I,indexedGaussianDisorder_law k I⟩
  have hJ : MeasurePreserving (indexedGaussianDisorder k J) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ J)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ J)) k)) :=
    ⟨indexedGaussianDisorder_measurable k J,indexedGaussianDisorder_law k J⟩
  exact (freshRoot_five_regroup _ _ _ _ _).comp
    ((MeasurePreserving.id (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))).prod
      (hI.prod hJ))

end SphericalPerceptronFreeEnergy
end

end OAI
