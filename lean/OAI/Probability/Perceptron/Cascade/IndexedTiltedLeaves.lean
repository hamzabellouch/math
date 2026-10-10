import Mathlib
import OAI.Probability.Perceptron.Cascade.DecoratedWeightedTotal
import OAI.Probability.Perceptron.Cascade.IndexedCascadeRegular

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def indexedShiftSum (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) →
    X×IndexedCascadeMarks S n → IndexedLeaf n → ℝ
  | 0,_,_,_ => 0
  | n+1,F,p,l => F 0 (p.1,(p.2 l.1 l.2.1).1)+
      indexedShiftSum step n (fun i => F i.succ)
        (step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2) l.2.2

lemma indexedShiftSum_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (Function.uncurry (indexedShiftSum step n F)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply measurable_from_prod_countable_left
    intro l
    change Measurable (fun p : X×(ℕ → ℕ → S×IndexedCascadeMarks S n) =>
      F 0 (p.1,(p.2 l.1 l.2.1).1)+indexedShiftSum step n (fun i => F i.succ)
        (step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2) l.2.2)
    exact ((hF 0).comp (by fun_prop)).add
      ((ih _ (fun i => hF i.succ)).comp (show Measurable
        (fun p : X×(ℕ → ℕ → S×IndexedCascadeMarks S n) =>
          ((step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2),l.2.2)) from by fun_prop))

lemma indexedShiftSum_telescoping (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (H : X → ℝ) (p : X×IndexedCascadeMarks S n)
    (l : IndexedLeaf n) :
    indexedShiftSum step n (finiteCascadeShifts ν step n z H) p l =
      H (indexedLeafState step n p l)-finiteCascadeLogRecursion ν step n z H p.1 := by
  induction n with
  | zero => simp [indexedShiftSum,indexedLeafState,finiteCascadeLogRecursion]
  | succ n ih =>
    simp only [indexedShiftSum,finiteCascadeShifts,Fin.cases_zero,Fin.cases_succ]
    rw [ih]
    change _ = H (indexedLeafState step n (step (p.1,(p.2 l.1 l.2.1).1),
      (p.2 l.1 l.2.1).2) l.2.2)-_
    ring

def indexedTiltedLeafMeasure (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (x : X) (b : IndexedCascadeBase n) (m : IndexedCascadeMarks S n) :
    Measure (IndexedLeaf n) :=
  (indexedLeafMeasure n b).withDensity
    (fun l => ENNReal.ofReal (Real.exp (indexedShiftSum step n F (x,m) l)))

lemma indexedLeafMeasure_shift_identity {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (m : IndexedCascadeMarks S n) (x : X) :
    decoratedWeightedTotalE step n F (x,indexedCascadeRealize n (b,m)) =
      ∫⁻ l, ENNReal.ofReal (Real.exp (indexedShiftSum step n F (x,m) l))
        ∂indexedLeafMeasure n b := by
  induction n generalizing x with
  | zero =>
    rw [indexedLeafMeasure_lintegral]
    simp [decoratedWeightedTotalE,indexedShiftSum,indexedLeafWeight,IndexedLeaf]
  | succ n ih =>
    rw [decoratedWeightedTotalE,indexedCascadeGood_countKernel hb]
    unfold indexedCascadeRealize
    dsimp only [Prod.fst,Prod.snd]
    have hm : Measurable (fun q : ℝ×(S×DecoratedCascade S n) =>
        ENNReal.ofReal (Real.exp (q.1+F 0 (x,q.2.1))) *
          decoratedWeightedTotalE step n (fun i => F i.succ) (step (x,q.2.1),q.2.2)) :=
      ((measurable_fst.add ((hF 0).comp (by fun_prop))).exp.ennreal_ofReal).mul
        ((decoratedWeightedTotalE_measurable step hs n _ (fun i => hF i.succ)).comp (by fun_prop))
    rw [indexedPoissonMeasure_lintegral _ hm,indexedLeafMeasure_lintegral_succ]
    apply tsum_congr
    intro i
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih _ (fun i => hF i.succ) _ (hb.2 i j.val) (m i j.val).2 (step (x,(m i j.val).1))]
    simp only [indexedShiftSum,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    exact mul_assoc _ _ _

lemma indexedTiltedLeafMeasure_total {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (m : IndexedCascadeMarks S n) (x : X) :
    (indexedTiltedLeafMeasure step n F x b m) univ =
      decoratedWeightedTotalE step n F (x,indexedCascadeRealize n (b,m)) := by
  rw [indexedTiltedLeafMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (indexedLeafMeasure_shift_identity hs n F hF b hb m x).symm

lemma indexedTiltedLeafMeasure_normalized_terminal (ν : ProbabilityMeasure S)
    (step : X×S → X) (n : ℕ) (z : Fin n → ℝ) (H : X → ℝ)
    (x : X) (b : IndexedCascadeBase n) (m : IndexedCascadeMarks S n) :
    normalizedMeasure (indexedTiltedLeafMeasure step n (finiteCascadeShifts ν step n z H) x b m) =
      normalizedMeasure ((indexedLeafMeasure n b).withDensity (fun l =>
        ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))))) := by
  have he : indexedTiltedLeafMeasure step n (finiteCascadeShifts ν step n z H) x b m =
      ENNReal.ofReal (Real.exp (-finiteCascadeLogRecursion ν step n z H x)) •
        ((indexedLeafMeasure n b).withDensity (fun l =>
          ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))))) := by
    unfold indexedTiltedLeafMeasure
    rw [← withDensity_smul _ (measurable_of_countable _)]
    apply withDensity_congr_ae
    filter_upwards [] with l
    simp only [indexedShiftSum_telescoping,sub_eq_add_neg,Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_comm _ _
  rw [he,normalizedMeasure_smul _ (by positivity) ENNReal.ofReal_ne_top]

end SphericalPerceptronFreeEnergy
end

end OAI
