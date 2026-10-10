import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedAncestry
import OAI.Probability.Perceptron.Variational.IndexedChildLaw
import OAI.Probability.Perceptron.Cascade.IndexedReplicaWeights
import OAI.Probability.Perceptron.Variational.IndexedTiltedRegular

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

section

def oneDecoratedVisit {X : Type} (h : X → ℝ≥0∞) : (n : ℕ) → DecoratedVisitShape X n
  | 0 => (1,h)
  | n+1 => [oneDecoratedVisit h n]

lemma oneDecoratedVisit_valid {X : Type} [MeasurableSpace X] {h : X → ℝ≥0∞}
    (hh : Measurable h) (n : ℕ) : (oneDecoratedVisit h n).Valid n := by
  induction n with
  | zero => exact ⟨le_rfl,hh⟩
  | succ n ih => exact ⟨by simp [oneDecoratedVisit],by simpa [oneDecoratedVisit] using ih⟩

lemma oneDecoratedVisit_count {X : Type} (h : X → ℝ≥0∞) (n : ℕ) :
    cascadeVisitCount n ((oneDecoratedVisit h n).bare n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [oneDecoratedVisit,DecoratedVisitShape.bare,cascadeVisitCount] using ih

lemma oneDecoratedVisit_likelihood {X : Type} (h : X → ℝ≥0∞) (n : ℕ)
    (z : Fin n → ℝ) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : a < 1) :
    cascadeShapeLikelihood n z a ((oneDecoratedVisit h n).bare n) = 1 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [oneDecoratedVisit,DecoratedVisitShape.bare,List.map_cons,List.map_nil,
      cascadeShapeLikelihood,List.prod_cons,List.prod_nil,mul_one]
    rw [ih (fun i => z i.succ) (fun i => hz1 i.succ) (z 0) (hz1 0)]
    simp only [oneDecoratedVisit_count,Nat.cast_one,stableEppfValue_singleton_one ha (hz1 0),
      ENNReal.ofReal_one,one_mul]

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedOneVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (h : X → ℝ≥0∞) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' l, indexedTiltedProbability step n F p l * h (indexedLeafState step n (p.1,p.2.2) l)

omit [Nonempty S] in
lemma indexedOneVisit_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    {h : X → ℝ≥0∞} (hh : Measurable h) : Measurable (indexedOneVisit step n F h) := by
  apply Measurable.tsum
  intro l
  exact ((indexedTiltedProbability_measurable hs n F hF).comp (measurable_id.prodMk measurable_const)).mul
    (hh.comp ((indexedLeafState_measurable hs n).comp (show Measurable
      (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) => ((p.1,p.2.2),l)) from by fun_prop)))

omit [Nonempty S] in
lemma indexedOneVisit_zero (step : X×S → X) (F : Fin 0 → X×S → ℝ)
    (h : X → ℝ≥0∞) (p : X×(IndexedCascadeBase 0×IndexedCascadeMarks S 0)) :
    indexedOneVisit step 0 F h p = h p.1 := by
  simp [indexedOneVisit,indexedTiltedProbability,indexedTiltedTotal,indexedTiltedWeight,
    indexedLeafWeight,indexedLeafState,indexedShiftSum,IndexedLeaf]

omit [Nonempty S] in
lemma indexedOneVisit_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (h : X → ℝ≥0∞) (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) :
    indexedOneVisit step (n+1) F h p =
      ∑' a, indexedBranchProbability step n F p a * indexedOneVisit step n (fun i => F i.succ) h
        (indexedChildPoint step n p a.1 a.2.val) := by
  rw [indexedOneVisit,indexedTiltedProbability_tsum_succ step n F p hc]
  rfl

lemma indexedOneVisit_eq_shape (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
      indexedOneVisit step n F h (x,p) =
        decoratedShapeProbability ν step n z F (oneDecoratedVisit h n) (x,indexedCascadeRealize n p) := by
  induction n generalizing x with
  | zero => exact ae_of_all _ fun p => indexedOneVisit_zero step F h (x,p)
  | succ n ih =>
    have hzt : StrictMono (fun i : Fin n => z i.succ) := fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
    have he := indexedCascade_ae_children ν step hs n z
      (fun p => indexedOneVisit step n (fun i => F i.succ) h p =
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
          (oneDecoratedVisit h n) (p.1,indexedCascadeRealize n p.2))
      (measurableSet_eq_fun (indexedOneVisit_measurable hs n _ (fun i => hF i.succ) hh)
        ((decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) _
          (oneDecoratedVisit_valid hh n)).comp
          (measurable_fst.prodMk ((indexedCascadeRealize_measurable n).comp measurable_snd))))
      (fun y => ih _ hzt (fun i => hz0 i.succ) (fun i => hz1 i.succ) _ (fun i => hF i.succ)
        (fun i => hI i.succ) (fun i => hM i.succ) y) x
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
    filter_upwards [he,hc,hj,hb] with p he hc hj hb
    rw [indexedOneVisit_succ step n F h (x,p) hc,oneDecoratedVisit,
      indexedShapeRoot_singleton ν step hs n z F hF (x,p) hb hc hj _ (oneDecoratedVisit_valid hh n),
      oneDecoratedVisit_count]
    simp only [pow_one]
    apply tsum_congr
    intro a
    exact congrArg (fun t => indexedBranchProbability step n F (x,p) a * t)
      (he a.1 a.2.val)

end

def twoDecoratedVisit {X : Type} (h k : X → ℝ≥0∞) : (n : ℕ) → Fin (n+1) → DecoratedVisitShape X n
  | 0,_ => (2,fun x => h x*k x)
  | n+1,d => Fin.cases [oneDecoratedVisit h n,oneDecoratedVisit k n]
      (fun i => [twoDecoratedVisit h k n i]) d

lemma twoDecoratedVisit_valid {X : Type} [MeasurableSpace X] {h k : X → ℝ≥0∞}
    (hh : Measurable h) (hk : Measurable k) (n : ℕ) (d : Fin (n+1)) :
    (twoDecoratedVisit h k n d).Valid n := by
  induction n with
  | zero => exact ⟨by change 1 ≤ 2; omega,hh.mul hk⟩
  | succ n ih =>
    induction d using Fin.cases with
    | zero =>
      refine ⟨by simp [twoDecoratedVisit],?_⟩
      intro s hs
      simp only [twoDecoratedVisit,Fin.cases_zero,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl|rfl
      · exact oneDecoratedVisit_valid hh n
      · exact oneDecoratedVisit_valid hk n
    | succ d =>
      exact ⟨by simp [twoDecoratedVisit],by simpa [twoDecoratedVisit] using ih d⟩

lemma twoDecoratedVisit_count {X : Type} (h k : X → ℝ≥0∞) (n : ℕ) (d : Fin (n+1)) :
    cascadeVisitCount n ((twoDecoratedVisit h k n d).bare n) = 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction d using Fin.cases with
    | zero => simp [twoDecoratedVisit,DecoratedVisitShape.bare,cascadeVisitCount,oneDecoratedVisit_count]
    | succ d => simpa [twoDecoratedVisit,DecoratedVisitShape.bare,cascadeVisitCount] using ih d

lemma activeRoot_eq_iff {n : ℕ} (b : IndexedCascadeBase (n+1))
    (a c : Σ i, Fin ((b i).1)) : a=c ↔ a.1=c.1 ∧ a.2.val=c.2.val := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rcases a with ⟨i,j⟩
    rcases c with ⟨i',j'⟩
    rintro ⟨rfl,hj⟩
    have : j=j' := Fin.ext hj
    subst j'
    rfl

lemma indexedCommonDepth_active_zero (n : ℕ) (b : IndexedCascadeBase (n+1))
    (a c : Σ i, Fin ((b i).1)) (l m : IndexedLeaf n) :
    indexedCommonDepth (n+1) (a.1,a.2.val,l) (c.1,c.2.val,m)=0 ↔ a≠c := by
  classical
  simp only [indexedCommonDepth, ← activeRoot_eq_iff]
  by_cases h : a=c <;> simp [h]

lemma indexedCommonDepth_active_succ (n : ℕ) (b : IndexedCascadeBase (n+1))
    (a c : Σ i, Fin ((b i).1)) (l m : IndexedLeaf n) (d : Fin (n+1)) :
    indexedCommonDepth (n+1) (a.1,a.2.val,l) (c.1,c.2.val,m)=d.succ ↔
      a=c ∧ indexedCommonDepth n l m=d := by
  classical
  simp only [indexedCommonDepth, ← activeRoot_eq_iff]
  by_cases h : a=c <;> simp [h,Ne.symm (Fin.succ_ne_zero d)]

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedTiltedPair_tsum_succ (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (f : IndexedLeaf (n+1) → IndexedLeaf (n+1) → ℝ≥0∞) :
    (∑' l, indexedTiltedProbability step (n+1) F p l *
      ∑' m, indexedTiltedProbability step (n+1) F p m * f l m) =
    ∑' a : Σ i, Fin ((p.2.1 i).1), ∑' b : Σ i, Fin ((p.2.1 i).1),
      indexedBranchProbability step n F p a * indexedBranchProbability step n F p b *
        ∑' l, indexedTiltedProbability step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val) l *
          ∑' m, indexedTiltedProbability step n (fun i => F i.succ) (indexedChildPoint step n p b.1 b.2.val) m *
            f (a.1,a.2.val,l) (b.1,b.2.val,m) := by
  rw [indexedTiltedProbability_tsum_succ step n F p hc]
  simp_rw [indexedTiltedProbability_tsum_succ step n F p hc]
  apply tsum_congr
  intro a
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro l
  apply tsum_congr
  intro m
  ac_rfl

def indexedTwoVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (h k : X → ℝ≥0∞) (d : Fin (n+1))
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' l, indexedTiltedProbability step n F p l * ∑' m, indexedTiltedProbability step n F p m *
    if indexedCommonDepth n l m=d then h (indexedLeafState step n (p.1,p.2.2) l)*
      k (indexedLeafState step n (p.1,p.2.2) m) else 0

omit [Nonempty S] in
lemma indexedTwoVisit_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    {h k : X → ℝ≥0∞} (hh : Measurable h) (hk : Measurable k) (d : Fin (n+1)) :
    Measurable (indexedTwoVisit step n F h k d) := by
  apply Measurable.tsum
  intro l
  apply Measurable.mul ((indexedTiltedProbability_measurable hs n F hF).comp
    (measurable_id.prodMk measurable_const))
  apply Measurable.tsum
  intro m
  apply Measurable.mul ((indexedTiltedProbability_measurable hs n F hF).comp
    (measurable_id.prodMk measurable_const))
  split_ifs
  · exact (hh.comp ((indexedLeafState_measurable hs n).comp (show Measurable
      (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) => ((p.1,p.2.2),l)) from by fun_prop))).mul
      (hk.comp ((indexedLeafState_measurable hs n).comp (show Measurable
      (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) => ((p.1,p.2.2),m)) from by fun_prop)))
  · exact measurable_const

omit [Nonempty S] in
lemma indexedTwoVisit_zero (step : X×S → X) (F : Fin 0 → X×S → ℝ)
    (h k : X → ℝ≥0∞) (d : Fin 1) (p : X×(IndexedCascadeBase 0×IndexedCascadeMarks S 0)) :
    indexedTwoVisit step 0 F h k d p = h p.1*k p.1 := by
  have hd : d=0 := Subsingleton.elim _ _
  simp [indexedTwoVisit,indexedTiltedProbability,indexedTiltedTotal,indexedTiltedWeight,
    indexedLeafWeight,indexedLeafState,indexedShiftSum,indexedCommonDepth,IndexedLeaf,hd]

omit [Nonempty S] in
lemma indexedTwoVisit_succ_zero (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ) (h k : X → ℝ≥0∞)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) :
    indexedTwoVisit step (n+1) F h k 0 p =
      ∑' a, indexedBranchProbability step n F p a * indexedOneVisit step n (fun i => F i.succ) h
        (indexedChildPoint step n p a.1 a.2.val) *
        ∑' b, if a=b then 0 else indexedBranchProbability step n F p b *
          indexedOneVisit step n (fun i => F i.succ) k (indexedChildPoint step n p b.1 b.2.val) := by
  classical
  rw [indexedTwoVisit,indexedTiltedPair_tsum_succ step n F p hc]
  apply tsum_congr
  intro a
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  simp only [indexedCommonDepth_active_zero n p.2.1]
  by_cases hab : a=b
  · simp [hab]
  · simp only [ite_eq_left hab,ite_eq_right hab,indexedOneVisit,indexedLeafState]
    simp_rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro m
    apply tsum_congr
    intro l
    dsimp only [indexedChildPoint]
    ac_rfl

omit [Nonempty S] in
lemma indexedTwoVisit_succ_succ (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ) (h k : X → ℝ≥0∞) (d : Fin (n+1))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) :
    indexedTwoVisit step (n+1) F h k d.succ p =
      ∑' a, (indexedBranchProbability step n F p a)^2 *
        indexedTwoVisit step n (fun i => F i.succ) h k d (indexedChildPoint step n p a.1 a.2.val) := by
  classical
  rw [indexedTwoVisit,indexedTiltedPair_tsum_succ step n F p hc]
  apply tsum_congr
  intro a
  rw [tsum_eq_single a]
  · simp only [indexedCommonDepth_active_succ n p.2.1,true_and,indexedTwoVisit,
      indexedLeafState,pow_two]
    rfl
  · intro b hb
    simp [indexedCommonDepth_active_succ n p.2.1,Ne.symm hb]

end SphericalPerceptronFreeEnergy

end

end OAI
