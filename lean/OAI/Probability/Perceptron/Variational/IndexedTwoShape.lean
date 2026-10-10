import Mathlib
import OAI.Probability.Perceptron.Variational.DecoratedShapeLaw
import OAI.Probability.Perceptron.Variational.IndexedVisit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma indexedTwoVisit_eq_shape (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h k : X → ℝ≥0∞) (hh : Measurable h) (hk : Measurable k) (d : Fin (n+1)) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
      indexedTwoVisit step n F h k d (x,p) =
        decoratedShapeProbability ν step n z F (twoDecoratedVisit h k n d) (x,indexedCascadeRealize n p) := by
  induction n generalizing x with
  | zero => exact ae_of_all _ fun p => indexedTwoVisit_zero step F h k d (x,p)
  | succ n ih =>
    have hzt : StrictMono (fun i : Fin n => z i.succ) := fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
    have hc := indexedCascade_ae_children ν step hs n z
      (fun p => 0 < (indexedTiltedTotal step n (fun i => F i.succ) p).toReal)
      (measurableSet_lt measurable_const ((indexedTiltedTotal_measurable hs n _ (fun i => hF i.succ)).ennreal_toReal))
      (fun y => indexedTiltedTotal_regular ν step hs n _ hzt (fun i => hz0 i.succ) (fun i => hz1 i.succ)
        _ (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ) y) x
    have hj := indexedCenteredRoot_simple ν step hs n z hz hz0 hz1 F hF hI hM x
    have hb := (measurePreserving_fst
      (μ := (indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))))
      (ν := (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))))).quasiMeasurePreserving.ae
        (indexedCascadeGood_ae (n+1) z hz0 hz1)
    induction d using Fin.cases with
    | zero =>
      have he (f : X → ℝ≥0∞) (hf : Measurable f) := indexedCascade_ae_children ν step hs n z
        (fun p => indexedOneVisit step n (fun i => F i.succ) f p =
          decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
            (oneDecoratedVisit f n) (p.1,indexedCascadeRealize n p.2))
        (measurableSet_eq_fun (indexedOneVisit_measurable hs n _ (fun i => hF i.succ) hf)
          ((decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) _
            (oneDecoratedVisit_valid hf n)).comp
            (measurable_fst.prodMk ((indexedCascadeRealize_measurable n).comp measurable_snd))))
        (fun y => indexedOneVisit_eq_shape ν step hs n _ hzt (fun i => hz0 i.succ)
          (fun i => hz1 i.succ) _ (fun i => hF i.succ) (fun i => hI i.succ)
          (fun i => hM i.succ) f hf y) x
      filter_upwards [he h hh,he k hk,hc,hj,hb] with p hh' hk' hc hj hb
      rw [indexedTwoVisit_succ_zero step n F h k (x,p) hc,twoDecoratedVisit,Fin.cases_zero,
        indexedShapeRoot_pair ν step hs n z F hF (x,p) hb hc hj _ _
          (oneDecoratedVisit_valid hh n) (oneDecoratedVisit_valid hk n),oneDecoratedVisit_count,
        oneDecoratedVisit_count]
      simp only [pow_one]
      apply tsum_congr
      intro a
      have hea := hh' a.1 a.2.val
      change indexedOneVisit step n _ h (indexedChildPoint step n (x,p) a.1 a.2.val) = _ at hea
      rw [hea]
      congr 1
      apply tsum_congr
      intro b
      split_ifs
      · rfl
      · exact congrArg (fun t => indexedBranchProbability step n F (x,p) b*t) (hk' b.1 b.2.val)
    | succ d =>
      have he := indexedCascade_ae_children ν step hs n z
        (fun p => indexedTwoVisit step n (fun i => F i.succ) h k d p =
          decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
            (twoDecoratedVisit h k n d) (p.1,indexedCascadeRealize n p.2))
        (measurableSet_eq_fun (indexedTwoVisit_measurable hs n _ (fun i => hF i.succ) hh hk d)
          ((decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) _
            (twoDecoratedVisit_valid hh hk n d)).comp
            (measurable_fst.prodMk ((indexedCascadeRealize_measurable n).comp measurable_snd))))
        (fun y => ih _ hzt (fun i => hz0 i.succ) (fun i => hz1 i.succ) _ (fun i => hF i.succ)
          (fun i => hI i.succ) (fun i => hM i.succ) d y) x
      filter_upwards [he,hc,hj,hb] with p he hc hj hb
      rw [indexedTwoVisit_succ_succ step n F h k d (x,p) hc,twoDecoratedVisit,Fin.cases_succ,
        indexedShapeRoot_singleton ν step hs n z F hF (x,p) hb hc hj _ (twoDecoratedVisit_valid hh hk n d),
        twoDecoratedVisit_count]
      apply tsum_congr
      intro a
      exact congrArg (fun t => (indexedBranchProbability step n F (x,p) a)^2*t) (he a.1 a.2.val)

lemma decoratedBiasedLaw_zero (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ) (x : X) :
    decoratedBiasedLaw ν step n z F x 0 =
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  simp [decoratedBiasedLaw,normalizedMeasure]

lemma indexedShapeProbability_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (v : DecoratedVisitShape X n) (hv : v.Valid n) (x : X) :
    (∫⁻ p, decoratedShapeProbability ν step n z F v (x,indexedCascadeRealize n p)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      cascadeShapeLikelihood n z 0 (v.bare n)*decoratedShapeMarkValue ν step n z F v x := by
  have hm : Measurable (fun η : DecoratedCascade S n =>
      decoratedShapeProbability ν step n z F v (x,η)) :=
    (decoratedShapeProbability_measurable ν step hs n z F hF v hv).comp
    (show Measurable (fun η : DecoratedCascade S n => (x,η)) from by fun_prop)
  rw [← lintegral_map hm (indexedCascadeRealize_measurable n),indexedCascadeRealize_law ν n z,
    ← decoratedBiasedLaw_zero ν step n z F x]
  exact decoratedShapeProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM 0 hz0 v hv x

lemma indexedOneVisit_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    (∫⁻ p, indexedOneVisit step n F h (x,p)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      decoratedShapeMarkValue ν step n z F (oneDecoratedVisit h n) x := by
  rw [lintegral_congr_ae (indexedOneVisit_eq_shape ν step hs n z hz hz0 hz1 F hF hI hM h hh x),
    indexedShapeProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM _ (oneDecoratedVisit_valid hh n) x,
    oneDecoratedVisit_likelihood h n z hz1 0 zero_lt_one,one_mul]

lemma indexedTwoVisit_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h k : X → ℝ≥0∞) (hh : Measurable h) (hk : Measurable k) (d : Fin (n+1)) (x : X) :
    (∫⁻ p, indexedTwoVisit step n F h k d (x,p)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      cascadeShapeLikelihood n z 0 ((twoDecoratedVisit h k n d).bare n) *
        decoratedShapeMarkValue ν step n z F (twoDecoratedVisit h k n d) x := by
  rw [lintegral_congr_ae (indexedTwoVisit_eq_shape ν step hs n z hz hz0 hz1 F hF hI hM h k hh hk d x)]
  exact indexedShapeProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM _
    (twoDecoratedVisit_valid hh hk n d) x

end SphericalPerceptronFreeEnergy

end

end OAI
