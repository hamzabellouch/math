import Mathlib
import OAI.Probability.Perceptron.Variational.FocusedRootProbability

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology

def indexedSampleFocused (n d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n)
    (b : IndexedCascadeBase n) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    ((∏ i, (indexedLeafProbability n b) {xs i}) *
      if CascadeShapeMatches n s xs then 1 else 0) *
        ∑' l : IndexedLeaf n, (indexedLeafProbability n b) {l} *
          if d ≤ (indexedCommonDepth n (xs (cascadeShapeFocus n s hs)) l).val then 1 else 0

lemma indexedSampleFocused_measurable (n d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n) :
    Measurable (indexedSampleFocused n d s hs) := by
  unfold indexedSampleFocused
  refine Measurable.tsum (fun xs => ?_)
  exact ((Finset.measurable_prod Finset.univ (fun i _ =>
    (Measure.measurable_coe (measurableSet_singleton (xs i))).comp
      (indexedLeafProbability_measurable n))).mul_const _).mul
        (Measurable.tsum (fun l => ((Measure.measurable_coe (measurableSet_singleton l)).comp
          (indexedLeafProbability_measurable n)).mul_const _))

lemma indexedFocusedVisit_zero_eq_sample {X S : Type} [MeasurableSpace X]
    [MeasurableSpace S] [Nonempty S] (step : X×S → X) (n d : ℕ)
    (s : CascadeVisitShape n) (hs : s.Valid n)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (hp : 0 < ((indexedLeafMeasure n p.2.1) univ).toReal) :
    indexedFocusedVisit step n (fun _ _ => 0) d s hs p = indexedSampleFocused n d s hs p.2.1 := by
  simp only [indexedFocusedVisit,indexedClassMass,indexedSampleFocused,
    indexedTiltedProbability_zero step n p hp]

lemma indexedSampleFocused_eq_measure (n d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n)
    (b : IndexedCascadeBase n) :
    indexedSampleFocused n d s hs b =
      ((Measure.pi (fun _ : CascadeShapeReplicas n s => indexedLeafProbability n b)).prod
        (indexedLeafProbability n b))
          {p | CascadeShapeMatches n s p.1 ∧
            d ≤ (indexedCommonDepth n (p.1 (cascadeShapeFocus n s hs)) p.2).val} := by
  rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet),lintegral_countable',
    ENNReal.tsum_prod']
  unfold indexedSampleFocused
  apply tsum_congr
  intro xs
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  rw [← Set.singleton_prod_singleton,Measure.prod_prod,Measure.pi_singleton]
  simp only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply]
  split_ifs <;> simp_all

theorem indexedSampleFocused_integral (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hs : s.Valid n) :
    (∫⁻ b, indexedSampleFocused n d s hs b ∂indexedCascadeBaseLaw n z) =
      cascadeShapeLikelihood n z 0 s *
        ENNReal.ofReal (focusedShapeNumerator n z 0 d s/(cascadeVisitCount n s:ℝ)) := by
  let ν : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩
  let step : Unit×Unit → Unit := fun _ => ()
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks Unit n))
  have he := indexedFocusedVisit_integral ν step measurable_const n z hz hz0 hz1
    (fun _ _ => 0) (fun _ => measurable_const)
    (by intro i x; simp only [mul_zero, Real.exp_zero]; exact integrable_const 1)
    (by intro i x; simp) d hd s hs ()
  have ha : ∀ᵐ p ∂B.prod M,
      indexedFocusedVisit step n (fun _ _ => 0) d s hs ((),p) = indexedSampleFocused n d s hs p.1 := by
    filter_upwards [(measurePreserving_fst (μ := B) (ν := M)).quasiMeasurePreserving.ae
      (indexedLeafMeasure_regular n z hz hz0 hz1)] with p hp
    exact indexedFocusedVisit_zero_eq_sample step n d s hs ((),p) hp
  rw [lintegral_congr_ae ha] at he
  have hprod := lintegral_prod (μ := B) (ν := M)
    (fun p : IndexedCascadeBase n×IndexedCascadeMarks Unit n => indexedSampleFocused n d s hs p.1)
    ((indexedSampleFocused_measurable n d s hs).comp measurable_fst).aemeasurable
  rw [hprod] at he
  simpa only [lintegral_const,measure_univ,mul_one,B,M] using he

def cascadeFocusCount (n d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n) : ℝ :=
  ∑ i : CascadeShapeReplicas n s,
    if d ≤ (indexedCommonDepth n (cascadeShapeLeaves n s (cascadeShapeFocus n s hs))
      (cascadeShapeLeaves n s i)).val then 1 else 0

lemma cascadeFocusCount_zero (n : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n) :
    cascadeFocusCount n 0 s hs = cascadeVisitCount n s := by
  simp [cascadeFocusCount,cascadeShapeReplicas_card]

lemma cascadeFocusCount_succ (n d : ℕ) (s : CascadeVisitShape n)
    (ss : List (CascadeVisitShape n)) (hs : CascadeVisitShape.Valid (n+1) (s::ss)) :
    cascadeFocusCount (n+1) (d+1) (s::ss) hs =
      cascadeFocusCount n d s (hs.2 s (by simp)) := by
  classical
  unfold cascadeFocusCount
  change (∑ i : (Σ i : Fin (ss.length+1), CascadeShapeReplicas n (s::ss)[i]), _) = _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single 0]
  · apply Finset.sum_congr rfl
    intro i _hi
    simp only [cascadeShapeFocus_cons,cascadeShapeLeaves,indexedCommonDepth,
      and_self,↓reduceIte,Fin.val_succ,Nat.add_le_add_iff_right]
    rfl
  · intro i _hi hne
    apply Finset.sum_eq_zero
    intro j _hj
    have hn : (0:ℕ) ≠ i.val := fun h => hne (Fin.ext h.symm)
    simp only [cascadeShapeFocus_cons,cascadeShapeLeaves,indexedCommonDepth,
      Fin.val_zero,hn,false_and,↓reduceIte,Nat.not_add_one_le_zero]
  · simp

lemma focusedShapeNumerator_eq_count (n : ℕ) (z : Fin n → ℝ) (a : ℝ)
    (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hs : s.Valid n) :
    focusedShapeNumerator n z a d s = cascadeFocusCount n d s hs -
      (if h : d = 0 then a else z ⟨d-1,by omega⟩) := by
  induction d generalizing n a with
  | zero => simp [focusedShapeNumerator,cascadeFocusCount_zero]
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases s with
      | nil => exact (hs.1 rfl).elim
      | cons s ss =>
        rw [focusedShapeNumerator,cascadeFocusCount_succ]
        rw [ih n (fun i => z i.succ) (z 0) (by omega) s (hs.2 s (by simp))]
        cases d with
        | zero => simp
        | succ d => simp

end SphericalPerceptronFreeEnergy
end

end OAI
