import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedLeafTotal
import OAI.Probability.Perceptron.Variational.IntegrableGibbs
import OAI.Probability.Perceptron.Variational.IndexedPathCorrelation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma tiltLaw_eq_normalized_exp {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (H : A→ℝ)
    (hi : Integrable (fun x => Real.exp (H x)) μ) :
    tiltLaw μ H 1 = normalizedMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) := by
  unfold tiltLaw normalizedMeasure tiltPartition
  simp only [one_mul]
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexed_terminal_tiltLaw (ν : ProbabilityMeasure S) (step : X×S→X)
    (n : ℕ) (z : Fin n→ℝ) (H : X→ℝ) (x : X) (b : IndexedCascadeBase n)
    (m : IndexedCascadeMarks S n) (hb : 0<((indexedLeafMeasure n b) univ).toReal)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,m) l)))
      (indexedLeafProbability n b)) :
    tiltLaw (indexedLeafProbability n b) (fun l => H (indexedLeafState step n (x,m) l)) 1 =
      normalizedMeasure (indexedTiltedLeafMeasure step n (finiteCascadeShifts ν step n z H) x b m) := by
  rw [indexedTiltedLeafMeasure_normalized_terminal,tiltLaw_eq_normalized_exp _ _ hi,
    indexedLeafProbability,ite_eq_left hb,withDensity_smul_measure]
  apply normalizedMeasure_smul
  · exact ENNReal.inv_ne_zero.mpr (ENNReal.toReal_pos_iff.mp hb).2.ne
  · exact ENNReal.inv_ne_top.mpr (ENNReal.toReal_pos_iff.mp hb).1.ne'

lemma indexed_terminal_lintegral (ν : ProbabilityMeasure S) (step : X×S→X)
    (n : ℕ) (z : Fin n→ℝ) (H : X→ℝ) (x : X) (b : IndexedCascadeBase n)
    (m : IndexedCascadeMarks S n) (hb : 0<((indexedLeafMeasure n b) univ).toReal)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,m) l)))
      (indexedLeafProbability n b)) (f : IndexedLeaf n→ℝ≥0∞) :
    (∫⁻ l, f l ∂tiltLaw (indexedLeafProbability n b)
      (fun l => H (indexedLeafState step n (x,m) l)) 1) =
      ∑' l, indexedTiltedProbability step n (finiteCascadeShifts ν step n z H) (x,(b,m)) l*f l := by
  rw [indexed_terminal_tiltLaw ν step n z H x b m hb hi]
  exact indexedTiltedProbability_lintegral step n (finiteCascadeShifts ν step n z H) (x,(b,m)) f

variable [Nonempty S]

omit [Nonempty S] in
lemma indexed_terminal_oneState (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (z : Fin n→ℝ) (H : X→ℝ) (hH : Measurable H) (x : X) (b : IndexedCascadeBase n)
    (m : IndexedCascadeMarks S n) (hb : 0<((indexedLeafMeasure n b) univ).toReal)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,m) l)))
      (indexedLeafProbability n b)) :
    (tiltLaw (indexedLeafProbability n b) (fun l => H (indexedLeafState step n (x,m) l)) 1).map
      (indexedLeafState step n (x,m)) =
      indexedOneStateKernel step hs n (finiteCascadeShifts ν step n z H)
        (finiteCascadeShifts_measurable ν step hs n z hH) x (b,m) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_of_countable _),indexed_terminal_lintegral ν step n z H x b m hb hi,
    indexedOneStateKernel,atomicVisitKernel_lintegral _ _ _ _ _ hf]

lemma indexed_terminal_exp_integrable_ae (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (H : X→ℝ) (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
      Integrable (fun l => Real.exp (H (indexedLeafState step n (x,p.2) l)))
        (indexedLeafProbability n p.1) := by
  have hnorm := finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz0 i).ne') H hI
  have ht := indexedTiltedTotal_regular ν step hs n z hz hz0 hz1
    (finiteCascadeShifts ν step n z H) (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i x => (hnorm i x).1) (fun i x => (hnorm i x).2) x
  have hb := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
    (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae (indexedLeafMeasure_regular n z hz hz0 hz1)
  have hg := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
    (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae (indexedCascadeGood_ae n z hz0 hz1)
  filter_upwards [ht,hb,hg] with p ht hb hg
  refine ⟨(measurable_of_countable _).aestronglyMeasurable,?_⟩
  simp only [HasFiniteIntegral,Real.enorm_eq_ofReal (Real.exp_pos _).le]
  rw [indexedLeafProbability_terminal_identity ν hs hH n p.1 hg hb p.2 x,
    decoratedTerminalTotalE_telescoping ν step H n z,
    ←indexedTiltedTotal_eq hs n (finiteCascadeShifts ν step n z H)
      (finiteCascadeShifts_measurable ν step hs n z hH) (x,p) hg]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.toReal_pos_iff.mp hb).1)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.toReal_pos_iff.mp ht).2)

omit [Nonempty S] in
lemma indexed_terminal_pairState (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (z : Fin n→ℝ) (H : X→ℝ) (hH : Measurable H) (x : X) (b : IndexedCascadeBase n)
    (m : IndexedCascadeMarks S n) (hb : 0<((indexedLeafMeasure n b) univ).toReal)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,m) l)))
      (indexedLeafProbability n b)) (d : Fin (n+1)) :
    let μ := tiltLaw (indexedLeafProbability n b) (fun l => H (indexedLeafState step n (x,m) l)) 1
    ((μ.prod μ).restrict {l : IndexedLeaf n×IndexedLeaf n | indexedCommonDepth n l.1 l.2=d}).map
      (fun l => (indexedLeafState step n (x,m) l.1,indexedLeafState step n (x,m) l.2)) =
      indexedPairStateKernel step hs n (finiteCascadeShifts ν step n z H)
        (finiteCascadeShifts_measurable ν step hs n z hH) x d (b,m) := by
  dsimp only
  let μ := tiltLaw (indexedLeafProbability n b) (fun l => H (indexedLeafState step n (x,m) l)) 1
  have : IsProbabilityMeasure μ := tilt_law_probability_of_integrable _
    (by simpa only [one_mul] using hi)
  change ((μ.prod μ).restrict _).map _ = _
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_of_countable _),
    ←lintegral_indicator ((Set.to_countable _).measurableSet),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp only [Set.indicator,Set.mem_ofPred_eq]
  change (∫⁻ a, (∫⁻ c, (if indexedCommonDepth n a c=d then
      f (indexedLeafState step n (x,m) a,indexedLeafState step n (x,m) c) else 0) ∂μ) ∂μ) = _
  dsimp only [μ]
  simp_rw [indexed_terminal_lintegral ν step n z H x b m hb hi]
  rw [indexedPairStateKernel,atomicVisitKernel_lintegral _ _ _ _ _ hf,ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro c
  simp only [indexedPairStateWeight]
  split_ifs <;> simp [mul_assoc]

lemma indexed_terminal_pair_integral (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (H : X→ℝ) (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ y, |f y|≤C) :
    (∫ p, (∫ l : IndexedLeaf n×IndexedLeaf n,
        f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2)
      ∂((tiltLaw (indexedLeafProbability n p.1)
          (fun a => H (indexedLeafState step n (x,p.2) a)) 1).prod
        (tiltLaw (indexedLeafProbability n p.1)
          (fun a => H (indexedLeafState step n (x,p.2) a)) 1)).restrict
          {l | indexedCommonDepth n l.1 l.2=d})
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      (twoVisitMass n z d).toReal * pathCorrelation n
        (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f d x := by
  have hnorm := finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz0 i).ne') H hI
  rw [←indexedPairState_integral ν step hs n z hz hz0 hz1
    (finiteCascadeShifts ν step n z H) (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i x => (hnorm i x).1) (fun i x => (hnorm i x).2) x d f hf C hC hfB]
  apply integral_congr_ae
  have hb := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
    (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae
      (indexedLeafMeasure_regular n z hz hz0 hz1)
  filter_upwards [hb,indexed_terminal_exp_integrable_ae ν step hs n z hz hz0 hz1 H hH hI x]
    with p hb hi
  rw [←indexed_terminal_pairState ν step hs n z H hH x p.1 p.2 hb hi d]
  exact (integral_map (measurable_of_countable
    (fun l : IndexedLeaf n×IndexedLeaf n =>
      (indexedLeafState step n (x,p.2) l.1,indexedLeafState step n (x,p.2) l.2))).aemeasurable
    ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).aestronglyMeasurable).symm

end SphericalPerceptronFreeEnergy
end

end OAI
