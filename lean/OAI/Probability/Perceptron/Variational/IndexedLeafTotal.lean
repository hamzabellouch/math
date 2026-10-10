import Mathlib
import OAI.Probability.Perceptron.Cascade.DecoratedWeightedTotal
import OAI.Probability.Perceptron.Cascade.IndexedCascadeRegular

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma decoratedTerminalTotalE_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) : Measurable (decoratedTerminalTotalE step H n) := by
  have he : decoratedTerminalTotalE step H n = fun p =>
      ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step n (fun _ => 0) H p.1)) *
        decoratedWeightedTotalE step n (finiteCascadeShifts ν step n (fun _ => 0) H) p := by
    funext p
    exact decoratedTerminalTotalE_telescoping ν step H n (fun _ => 0) p
  rw [he]
  exact (((finiteCascadeLogRecursion_measurable ν step hs n _ hH).comp measurable_fst).exp.ennreal_ofReal).mul
    (decoratedWeightedTotalE_measurable step hs n _ (finiteCascadeShifts_measurable ν step hs n _ hH))

lemma indexedLeafMeasure_terminal_identity {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (m : IndexedCascadeMarks S n) (x : X) :
    decoratedTerminalTotalE step H n (x,indexedCascadeRealize n (b,m)) =
      ∫⁻ l, ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))) ∂indexedLeafMeasure n b := by
  induction n generalizing x with
  | zero =>
    rw [indexedLeafMeasure_lintegral]
    simp [decoratedTerminalTotalE,indexedLeafWeight,indexedLeafState,IndexedLeaf]
  | succ n ih =>
    rw [decoratedTerminalTotalE,indexedCascadeGood_countKernel hb]
    unfold indexedCascadeRealize
    dsimp only [Prod.fst,Prod.snd]
    have hm : Measurable (fun q : ℝ×(S×DecoratedCascade S n) => ENNReal.ofReal (Real.exp q.1) *
        decoratedTerminalTotalE step H n (step (x,q.2.1),q.2.2)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedTerminalTotalE_measurable ν hs hH n).comp (by fun_prop))
    rw [indexedPoissonMeasure_lintegral _ hm,
      indexedLeafMeasure_lintegral_succ]
    apply tsum_congr
    intro i
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    exact ih (((b i).2 j.val).2) (hb.2 i j.val) (m i j.val).2 (step (x,(m i j.val).1))

lemma indexedLeafMeasure_regular (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    ∀ᵐ b ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)),
      0 < ((indexedLeafMeasure n b) univ).toReal := by
  let ν : ProbabilityMeasure Unit := ⟨Measure.dirac (),inferInstance⟩
  let step : Unit×Unit → Unit := fun _ => ()
  have hs : Measurable step := measurable_const
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks Unit n))
  let D := (decoratedCascadeLaw ν n z : Measure (DecoratedCascade Unit n))
  have hi := decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i x; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i x; simp) ()
  have hp := hi.symm.ae_snd measurableSet_Ioi (cascadeTotal_regular n z hz hz0 hz1).1
  have hR : MeasurePreserving (indexedCascadeRealize (S := Unit) n) (B.prod M) D :=
    ⟨indexedCascadeRealize_measurable n,indexedCascadeRealize_law ν n z⟩
  have ht := hR.quasiMeasurePreserving.ae hp
  have hg : ∀ᵐ p ∂B.prod M, IndexedCascadeGood n p.1 :=
    (measurePreserving_fst (μ := B) (ν := M)).quasiMeasurePreserving.ae (indexedCascadeGood_ae n z hz0 hz1)
  have he : ∀ᵐ p ∂B.prod M, 0 < ((indexedLeafMeasure n p.1) univ).toReal := by
    filter_upwards [ht,hg] with p hp hg
    have h := indexedLeafMeasure_terminal_identity ν hs (H := fun _ => 0) measurable_const n p.1 hg p.2 ()
    simp only [decoratedTerminalTotalE_zero,Real.exp_zero,ENNReal.ofReal_one,lintegral_one] at h
    change 0 < (decoratedWeightedTotalE step n (fun _ _ => 0) ((),indexedCascadeRealize n p)).toReal at hp
    rwa [← h]
  exact (Measure.ae_ae_of_ae_prod he).mono fun b hb => hb.exists.choose_spec

def indexedLeafProbability (n : ℕ) (b : IndexedCascadeBase n) : Measure (IndexedLeaf n) :=
  if 0 < ((indexedLeafMeasure n b) univ).toReal then
    ((indexedLeafMeasure n b) univ)⁻¹ • indexedLeafMeasure n b
  else Measure.dirac (Classical.choice (indexedLeaf_nonempty n))

instance indexedLeafProbability_isProbability (n : ℕ) (b : IndexedCascadeBase n) :
    IsProbabilityMeasure (indexedLeafProbability n b) := by
  constructor
  by_cases h : 0 < ((indexedLeafMeasure n b) univ).toReal
  · rw [indexedLeafProbability,ite_eq_left h,Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.toReal_pos_iff.mp h).1.ne'
      (ENNReal.toReal_pos_iff.mp h).2.ne
  · simp [indexedLeafProbability,h]

lemma indexedLeafProbability_measurable (n : ℕ) : Measurable (indexedLeafProbability n) := by
  have hm := indexedLeafMeasure_measurable n
  have ht : Measurable (fun b => (indexedLeafMeasure n b) univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp hm
  apply Measurable.ite (measurableSet_lt measurable_const ht.ennreal_toReal)
  · apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ht.inv.mul ((Measure.measurable_coe hs).comp hm)
  · exact measurable_const

lemma indexedLeafProbability_lintegral (n : ℕ) (b : IndexedCascadeBase n)
    (hb : 0 < ((indexedLeafMeasure n b) univ).toReal) (f : IndexedLeaf n → ℝ≥0∞) :
    (∫⁻ l, f l ∂indexedLeafProbability n b) =
      ((indexedLeafMeasure n b) univ)⁻¹ * ∫⁻ l, f l ∂indexedLeafMeasure n b := by
  rw [indexedLeafProbability,ite_eq_left hb,lintegral_smul_measure,smul_eq_mul]

lemma indexedLeafProbability_terminal_identity {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (hb' : 0 < ((indexedLeafMeasure n b) univ).toReal)
    (m : IndexedCascadeMarks S n) (x : X) :
    (∫⁻ l, ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))) ∂indexedLeafProbability n b) =
      ((indexedLeafMeasure n b) univ)⁻¹ *
        decoratedTerminalTotalE step H n (x,indexedCascadeRealize n (b,m)) := by
  rw [indexedLeafProbability_lintegral n b hb',indexedLeafMeasure_terminal_identity ν hs hH n b hb]

end SphericalPerceptronFreeEnergy

end

end OAI
