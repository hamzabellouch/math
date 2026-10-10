import Mathlib
import OAI.Probability.Perceptron.Variational.MarkedBlockParameter
import OAI.Probability.Perceptron.Cascade.IndexedTiltedLeaves

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

section
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def indexedTiltedWeight (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (l : IndexedLeaf n) : ℝ≥0∞ :=
  (indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
    ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l))

def indexedTiltedTotal (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' l, indexedTiltedWeight step n F p l

def indexedTiltedProbability (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (l : IndexedLeaf n) : ℝ≥0∞ :=
  (indexedTiltedTotal step n F p)⁻¹ * indexedTiltedWeight step n F p l

lemma indexedTiltedWeight_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (Function.uncurry (indexedTiltedWeight step n F)) := by
  exact (((indexedLeafWeight_measurable n).comp (show Measurable
    (fun q : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×IndexedLeaf n =>
      (q.1.2.1,q.2)) from by fun_prop)).coe_nnreal_ennreal).mul
    (((indexedShiftSum_measurable hs n F hF).comp (show Measurable
      (fun q : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×IndexedLeaf n =>
        ((q.1.1,q.1.2.2),q.2)) from by fun_prop)).exp.ennreal_ofReal)

lemma indexedTiltedTotal_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (indexedTiltedTotal step n F) :=
  Measurable.tsum fun _ => (indexedTiltedWeight_measurable hs n F hF).comp
    (measurable_id.prodMk measurable_const)

lemma indexedTiltedProbability_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (Function.uncurry (indexedTiltedProbability step n F)) :=
  (((indexedTiltedTotal_measurable hs n F hF).comp measurable_fst).inv).mul
    (indexedTiltedWeight_measurable hs n F hF)

lemma indexedTiltedTotal_eq {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (hb : IndexedCascadeGood n p.2.1) :
    indexedTiltedTotal step n F p =
      decoratedWeightedTotalE step n F (p.1,indexedCascadeRealize n p.2) := by
  rw [indexedLeafMeasure_shift_identity hs n F hF p.2.1 hb p.2.2 p.1,
    indexedLeafMeasure_lintegral]
  rfl

omit [MeasurableSpace X] in
lemma indexedTiltedProbability_mass (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (hp : 0 < (indexedTiltedTotal step n F p).toReal) :
    ∑' l, indexedTiltedProbability step n F p l = 1 := by
  simp only [indexedTiltedProbability,ENNReal.tsum_mul_left]
  exact ENNReal.inv_mul_cancel (ENNReal.toReal_pos_iff.mp hp).1.ne'
    (ENNReal.toReal_pos_iff.mp hp).2.ne

omit [MeasurableSpace X] in
lemma indexedTiltedProbability_lintegral (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (f : IndexedLeaf n → ℝ≥0∞) :
    (∫⁻ l, f l ∂normalizedMeasure (indexedTiltedLeafMeasure step n F p.1 p.2.1 p.2.2)) =
      ∑' l, indexedTiltedProbability step n F p l*f l := by
  rw [normalizedMeasure,lintegral_smul_measure,smul_eq_mul,indexedTiltedLeafMeasure,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) (measurable_of_countable _),
    indexedLeafMeasure_lintegral,indexedLeafMeasure_lintegral,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  change (∑' l, (indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
    ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l)))⁻¹ *
      ((indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
        (ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l))*f l)) = _
  simp only [indexedTiltedProbability,indexedTiltedTotal,indexedTiltedWeight,mul_assoc]

omit [MeasurableSpace X] in
lemma indexedTiltedWeight_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (i j : ℕ) (l : IndexedLeaf n) :
    indexedTiltedWeight step (n+1) F p (i,j,l) =
      if j < (p.2.1 i).1 then ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
        indexedTiltedWeight step n (fun a => F a.succ)
          (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l else 0 := by
  by_cases hj : j<(p.2.1 i).1
  · simp only [indexedTiltedWeight,indexedLeafWeight,indexedShiftSum,ite_eq_left hj,
      ENNReal.coe_mul,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    change (ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1))*_)*(_*_) = _
    ac_rfl
  · simp [indexedTiltedWeight,indexedLeafWeight,indexedShiftSum,hj]

omit [MeasurableSpace X] in
lemma indexedTiltedWeight_tsum_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (f : IndexedLeaf (n+1) → ℝ≥0∞) :
    (∑' l, indexedTiltedWeight step (n+1) F p l*f l) =
      ∑' i, ∑ j : Fin ((p.2.1 i).1),
        ENNReal.ofReal (Real.exp (((p.2.1 i).2 j.val).1+F 0 (p.1,(p.2.2 i j.val).1)))*
          ∑' l, indexedTiltedWeight step n (fun a => F a.succ)
            (step (p.1,(p.2.2 i j.val).1),(((p.2.1 i).2 j.val).2,(p.2.2 i j.val).2)) l * f (i,j.val,l) := by
  change (∑' l : ℕ×ℕ×IndexedLeaf n, _) = _
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro i
  rw [ENNReal.tsum_prod']
  simp_rw [indexedTiltedWeight_succ]
  have he (j : ℕ) : (∑' l : IndexedLeaf n,
      (if j<(p.2.1 i).1 then ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
        indexedTiltedWeight step n (fun a => F a.succ)
          (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l else 0)*f (i,j,l)) =
      if j<(p.2.1 i).1 then ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
        ∑' l, indexedTiltedWeight step n (fun a => F a.succ)
          (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l*f (i,j,l) else 0 := by
    split_ifs with h
    · simp_rw [mul_assoc,ENNReal.tsum_mul_left]
    · simp
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range ((p.2.1 i).1)) (fun j hj => by simp [Finset.mem_range.not.mp hj])]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
      ∑' l, indexedTiltedWeight step n (fun a => F a.succ)
        (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l * f (i,j,l))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (Finset.mem_range.mp hj)]

omit [MeasurableSpace X] in
lemma indexedTiltedTotal_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1))) :
    indexedTiltedTotal step (n+1) F p =
      ∑' i, ∑ j : Fin ((p.2.1 i).1),
        ENNReal.ofReal (Real.exp (((p.2.1 i).2 j.val).1+F 0 (p.1,(p.2.2 i j.val).1)))*
          indexedTiltedTotal step n (fun a => F a.succ)
            (step (p.1,(p.2.2 i j.val).1),(((p.2.1 i).2 j.val).2,(p.2.2 i j.val).2)) := by
  simpa only [mul_one,indexedTiltedTotal] using indexedTiltedWeight_tsum_succ step n F p (fun _ => 1)

end
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedChildPoint (step : X×S → X) (n : ℕ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1))) (i j : ℕ) :
    X×(IndexedCascadeBase n×IndexedCascadeMarks S n) :=
  (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2))

def indexedRootPoint (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin (n+1) → ℝ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1)) : ℝ×(S×DecoratedCascade S n) :=
  let t := ((p.2.2 a.1 a.2.val).1,
    indexedCascadeRealize n ((((p.2.1 a.1).2 a.2.val).2,(p.2.2 a.1 a.2.val).2)))
  ((((p.2.1 a.1).2 a.2.val).1 + decoratedCenteredRoot ν step n z F (p.1,t)),t)

def indexedBranchWeight (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (((p.2.1 a.1).2 a.2.val).1+F 0 (p.1,(p.2.2 a.1 a.2.val).1)))*
    indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val)

def indexedBranchProbability (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1)) : ℝ≥0∞ :=
  (indexedTiltedTotal step (n+1) F p)⁻¹*indexedBranchWeight step n F p a

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedBranchWeight_tsum (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1))) :
    (∑' a, indexedBranchWeight step n F p a) = indexedTiltedTotal step (n+1) F p := by
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype,indexedBranchWeight,indexedChildPoint]
  exact (indexedTiltedTotal_succ step n F p).symm

lemma indexedRootPoint_weight (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (a : Σ i, Fin ((p.2.1 i).1)) :
    ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p a).1) =
      ENNReal.ofReal (Real.exp (-(Real.log (∫ t : S×DecoratedCascade S n,
        Real.exp (z 0*decoratedRootPotential step n F (p.1,t))
        ∂((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))))/z 0)))*
          indexedBranchWeight step n F p a := by
  have he := indexedTiltedTotal_eq hs n (fun i => F i.succ) (fun i => hF i.succ)
    (indexedChildPoint step n p a.1 a.2.val) (hb.2 a.1 a.2.val)
  dsimp only [indexedChildPoint] at he
  have hpos := hc a.1 a.2.val
  have hfinite := (ENNReal.toReal_pos_iff.mp hpos).2.ne
  simp only [indexedRootPoint,decoratedCenteredRoot,centeredLogMark,decoratedRootPotential,
    decoratedWeightedTotal,← he,indexedBranchWeight]
  let A := (((p.2.1 a.1).2 a.2.val).1)
  let B := F 0 (p.1,(p.2.2 a.1 a.2.val).1)
  let C := Real.log (∫ t : S×DecoratedCascade S n,
    Real.exp (z 0*decoratedRootPotential step n F (p.1,t))
      ∂((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))) / z 0
  let T := indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val)
  change ENNReal.ofReal (Real.exp (A + (B + Real.log T.toReal - C))) =
    ENNReal.ofReal (Real.exp (-C))*(ENNReal.ofReal (Real.exp (A+B))*T)
  rw [show A+(B+Real.log T.toReal-C) = -C+((A+B)+Real.log T.toReal) by ring,
    Real.exp_add,Real.exp_add,Real.exp_log hpos,
    ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_toReal hfinite]

lemma indexedRootPoint_probability (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (a : Σ i, Fin ((p.2.1 i).1)) :
    ((∑' b, ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p b).1))⁻¹)*
      ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p a).1) =
        indexedBranchProbability step n F p a := by
  simp_rw [indexedRootPoint_weight ν step hs n z F hF p hb hc,
    ENNReal.tsum_mul_left,indexedBranchWeight_tsum]
  rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
    (Or.inl ENNReal.ofReal_ne_top)]
  simp only [indexedBranchProbability]
  rw [mul_mul_mul_comm,ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
    ENNReal.ofReal_ne_top,one_mul]

end SphericalPerceptronFreeEnergy

end

end OAI
