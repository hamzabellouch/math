import Mathlib
import OAI.Probability.Perceptron.Variational.Shape

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical ENNReal NNReal BigOperators Topology

lemma indexedShiftSum_zero {X S : Type} [MeasurableSpace S] (step : X×S → X)
    (n : ℕ) (p : X×IndexedCascadeMarks S n) (l : IndexedLeaf n) :
    indexedShiftSum step n (fun _ _ => 0) p l = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indexedShiftSum, ih, add_zero]

lemma indexedTiltedWeight_zero {X S : Type} [MeasurableSpace S] (step : X×S → X)
    (n : ℕ) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (l : IndexedLeaf n) :
    indexedTiltedWeight step n (fun _ _ => 0) p l = indexedLeafWeight n p.2.1 l := by
  simp only [indexedTiltedWeight, indexedShiftSum_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]

lemma indexedTiltedTotal_zero {X S : Type} [MeasurableSpace S] (step : X×S → X)
    (n : ℕ) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) :
    indexedTiltedTotal step n (fun _ _ => 0) p = (indexedLeafMeasure n p.2.1) univ := by
  rw [← lintegral_one, indexedLeafMeasure_lintegral]
  simp only [indexedTiltedTotal, indexedTiltedWeight_zero, mul_one]

lemma indexedLeafMeasure_singleton (n : ℕ) (b : IndexedCascadeBase n) (l : IndexedLeaf n) :
    (indexedLeafMeasure n b) {l} = indexedLeafWeight n b l := by
  rw [indexedLeafMeasure, Measure.sum_apply _ (measurableSet_singleton l), tsum_eq_single l]
  · simp [Measure.smul_apply]
  · intro i hi
    simp [Measure.smul_apply, hi]

lemma indexedTiltedProbability_zero {X S : Type} [MeasurableSpace S] (step : X×S → X)
    (n : ℕ) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (hp : 0 < ((indexedLeafMeasure n p.2.1) univ).toReal) (l : IndexedLeaf n) :
    indexedTiltedProbability step n (fun _ _ => 0) p l =
      (indexedLeafProbability n p.2.1) {l} := by
  rw [indexedTiltedProbability, indexedTiltedTotal_zero, indexedTiltedWeight_zero,
    indexedLeafProbability, ite_eq_left hp, Measure.smul_apply, smul_eq_mul,
    indexedLeafMeasure_singleton]

def indexedSampleShape (n : ℕ) (s : CascadeVisitShape n) (b : IndexedCascadeBase n) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    (∏ i, (indexedLeafProbability n b) {xs i}) *
      if CascadeShapeMatches n s xs then 1 else 0

lemma indexedSampleShape_measurable (n : ℕ) (s : CascadeVisitShape n) :
    Measurable (indexedSampleShape n s) := by
  unfold indexedSampleShape
  refine Measurable.tsum (fun xs => ?_)
  exact (Finset.measurable_prod Finset.univ (fun i _ =>
    (Measure.measurable_coe (measurableSet_singleton (xs i))).comp
      (indexedLeafProbability_measurable n))).mul_const _

lemma indexedSampleShape_eq_measure (n : ℕ) (s : CascadeVisitShape n)
    (b : IndexedCascadeBase n) :
    indexedSampleShape n s b =
      (Measure.pi (fun _ : CascadeShapeReplicas n s => indexedLeafProbability n b))
        {xs | CascadeShapeMatches n s xs} := by
  classical
  rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet), lintegral_countable']
  unfold indexedSampleShape
  apply tsum_congr
  intro xs
  rw [Measure.pi_singleton]
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  split_ifs <;> simp

lemma indexedShapeVisit_zero_eq_sample {X S : Type} [MeasurableSpace X]
    [MeasurableSpace S] [Nonempty S] (step : X×S → X) (n : ℕ)
    (s : CascadeVisitShape n) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (hp : 0 < ((indexedLeafMeasure n p.2.1) univ).toReal) :
    indexedShapeVisit step n (fun _ _ => 0) s p = indexedSampleShape n s p.2.1 := by
  unfold indexedShapeVisit indexedSampleShape
  congr 1
  funext xs
  congr 1
  exact Finset.prod_congr rfl (fun i _ => indexedTiltedProbability_zero step n p hp (xs i))

theorem indexedSampleShape_integral (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (s : CascadeVisitShape n) (hs : s.Valid n) :
    (∫⁻ b, indexedSampleShape n s b ∂indexedCascadeBaseLaw n z) =
      cascadeShapeLikelihood n z 0 s := by
  let ν : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩
  let step : Unit×Unit → Unit := fun _ => ()
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks Unit n))
  have he := indexedShapeVisit_integral ν step measurable_const n z hz hz0 hz1
    (fun _ _ => 0) (fun _ => measurable_const)
    (by intro i x; simp only [mul_zero, Real.exp_zero]; exact integrable_const 1)
    (by intro i x; simp) s hs ()
  have ha : ∀ᵐ p ∂B.prod M,
      indexedShapeVisit step n (fun _ _ => 0) s ((),p) = indexedSampleShape n s p.1 := by
    filter_upwards [(measurePreserving_fst (μ := B) (ν := M)).quasiMeasurePreserving.ae
      (indexedLeafMeasure_regular n z hz hz0 hz1)] with p hp
    exact indexedShapeVisit_zero_eq_sample step n s ((),p) hp
  rw [lintegral_congr_ae ha] at he
  have hprod := lintegral_prod (μ := B) (ν := M)
    (fun p : IndexedCascadeBase n×IndexedCascadeMarks Unit n => indexedSampleShape n s p.1)
    ((indexedSampleShape_measurable n s).comp measurable_fst).aemeasurable
  rw [hprod] at he
  simpa only [lintegral_const, measure_univ, mul_one, B, M] using he

def cascadeShapeFocus : (n : ℕ) → (s : CascadeVisitShape n) → s.Valid n →
    CascadeShapeReplicas n s
  | 0, s, hs => ⟨0,hs⟩
  | n+1, ss, hs =>
    let hlen := List.length_pos_iff.mpr hs.1
    ⟨⟨0,hlen⟩, cascadeShapeFocus n ss[0] (hs.2 _ (List.getElem_mem hlen))⟩

lemma cascadeShapeFocus_cons (n : ℕ) (s : CascadeVisitShape n)
    (ss : List (CascadeVisitShape n)) (hs : CascadeVisitShape.Valid (n+1) (s::ss)) :
    cascadeShapeFocus (n+1) (s::ss) hs =
      ⟨0,cascadeShapeFocus n s (hs.2 s (by simp))⟩ := rfl

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedClassMass (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (d : ℕ) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (l : IndexedLeaf n) : ℝ≥0∞ :=
  ∑' m : IndexedLeaf n, indexedTiltedProbability step n F p m *
    if d ≤ (indexedCommonDepth n l m).val then 1 else 0

omit [Nonempty S] in
lemma indexedClassMass_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (d : ℕ) (l : IndexedLeaf n) : Measurable (fun p => indexedClassMass step n F d p l) := by
  unfold indexedClassMass
  exact Measurable.tsum (fun m =>
    ((indexedTiltedProbability_measurable hs n F hF).comp
      (measurable_id.prodMk (measurable_const (a := m)))).mul_const _)

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedClassMass_active_succ (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ) (d : ℕ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (a : Σ i, Fin ((p.2.1 i).1)) (l : IndexedLeaf n) :
    indexedClassMass step (n+1) F (d+1) p (a.1,a.2.val,l) =
      indexedBranchProbability step n F p a *
        indexedClassMass step n (fun i => F i.succ) d
          (indexedChildPoint step n p a.1 a.2.val) l := by
  unfold indexedClassMass
  rw [indexedTiltedProbability_tsum_succ step n F p hc]
  rw [tsum_eq_single a]
  · apply congrArg (fun v => indexedBranchProbability step n F p a * v)
    apply tsum_congr
    intro m
    simp only [indexedCommonDepth, and_self, ↓reduceIte, Fin.val_succ,
      Nat.add_le_add_iff_right]
  · intro b hb
    have hne : ¬ (a.1 = b.1 ∧ a.2.val = b.2.val) := by
      intro he
      exact hb ((activeRoot_eq_iff p.2.1 a b).mpr he).symm
    simp only [indexedCommonDepth, ite_eq_right hne, Fin.val_zero,
      Nat.not_add_one_le_zero, ↓reduceIte, mul_zero, tsum_zero]

def indexedFocusedVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    ((∏ i, indexedTiltedProbability step n F p (xs i)) *
      if CascadeShapeMatches n s xs then 1 else 0) *
        indexedClassMass step n F d p (xs (cascadeShapeFocus n s hs))

omit [Nonempty S] in
lemma indexedFocusedVisit_measurable (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n) :
    Measurable (indexedFocusedVisit step n F d s hs) := by
  unfold indexedFocusedVisit
  refine Measurable.tsum (fun xs => ?_)
  exact ((Finset.measurable_prod Finset.univ (fun i _ =>
    (indexedTiltedProbability_measurable hstep n F hF).comp
      (measurable_id.prodMk (measurable_const (a := xs i))))).mul_const _).mul
      (indexedClassMass_measurable step hstep n F hF d _)

end SphericalPerceptronFreeEnergy

end

end OAI
