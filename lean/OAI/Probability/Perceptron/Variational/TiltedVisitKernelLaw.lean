import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedTwoShape
import OAI.Probability.Perceptron.Variational.TiltedVisitKernel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [Nonempty S] in
lemma pathOneKernel_lintegral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    (∫⁻ y, h y ∂pathOneKernel n (fun i => tiltedStateStep ν step (z i) (F i)) x) =
      decoratedShapeMarkValue ν step n z F (oneDecoratedVisit h n) x := by
  induction n generalizing x with
  | zero =>
    simp only [pathOneKernel,Kernel.id_apply,decoratedShapeMarkValue,oneDecoratedVisit]
    exact lintegral_dirac' _ hh
  | succ n ih =>
    rw [pathOneKernel,Kernel.lintegral_comp _ _ _ hh]
    simp_rw [ih (fun i => z i.succ) (fun i => F i.succ) (fun i => hF i.succ)
      (fun i => hI i.succ) (fun i => hM i.succ)]
    rw [tiltedStateStep_lintegral ν step hs (z 0) (F 0) (hF 0) (hI 0) (hM 0) _
      (decoratedShapeMarkValue_measurable ν step hs n _ _ (fun i => hF i.succ) _
        (oneDecoratedVisit_valid hh n))]
    simp [decoratedShapeMarkValue,oneDecoratedVisit]

omit [Nonempty S] in
lemma pathPairKernel_lintegral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h k : X → ℝ≥0∞) (hh : Measurable h) (hk : Measurable k) (d : Fin (n+1)) (x : X) :
    (∫⁻ p, h p.1*k p.2 ∂pathPairKernel n (fun i => tiltedStateStep ν step (z i) (F i)) d x) =
      decoratedShapeMarkValue ν step n z F (twoDecoratedVisit h k n d) x := by
  have hg : Measurable (fun p : X×X => h p.1*k p.2) := (hh.comp measurable_fst).mul (hk.comp measurable_snd)
  induction n generalizing x with
  | zero =>
    rw [pathPairKernel,Kernel.lintegral_deterministic' _ hg]
    rfl
  | succ n ih =>
    have hκ i := tiltedStateStep_markov ν step hs (z i) (F i) (hF i) (hI i) (hM i)
    have := pathOneKernel_markov (n+1) (fun i => tiltedStateStep ν step (z i) (F i)) hκ
    induction d using Fin.cases with
    | zero =>
      simp only [pathPairKernel,Fin.cases_zero]
      rw [Kernel.lintegral_prod _ _ _ hg]
      simp_rw [lintegral_const_mul _ hk,lintegral_mul_const _ hh]
      rw [pathOneKernel_lintegral ν step hs (n+1) z F hF hI hM h hh x,
        pathOneKernel_lintegral ν step hs (n+1) z F hF hI hM k hk x]
      simp [decoratedShapeMarkValue,oneDecoratedVisit,twoDecoratedVisit]
    | succ d =>
      simp only [pathPairKernel,Fin.cases_succ]
      rw [Kernel.lintegral_comp _ _ _ hg]
      simp_rw [ih (fun i => z i.succ) (fun i => F i.succ) (fun i => hF i.succ)
        (fun i => hI i.succ) (fun i => hM i.succ) d]
      rw [tiltedStateStep_lintegral ν step hs (z 0) (F 0) (hF 0) (hI 0) (hM 0) _
        (decoratedShapeMarkValue_measurable ν step hs n _ _ (fun i => hF i.succ) _
          (twoDecoratedVisit_valid hh hk n d))]
      simp [decoratedShapeMarkValue,twoDecoratedVisit]

section
variable {P Y I : Type} [MeasurableSpace P] [MeasurableSpace Y] [Countable I]

def atomicVisitKernel (q : I → P → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    (s : I → P → Y) (hs : ∀ i, Measurable (s i)) : Kernel P Y :=
  ⟨fun p => Measure.sum (fun i => q i p • Measure.dirac (s i p)), by
    apply Measure.measurable_of_measurable_coe
    intro t ht
    simp only [Measure.sum_apply _ ht,Measure.smul_apply]
    exact Measurable.tsum (fun i => (hq i).mul ((Measure.measurable_coe ht).comp
      (Measure.measurable_dirac.comp (hs i))))⟩

lemma atomicVisitKernel_lintegral (q : I → P → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    (s : I → P → Y) (hs : ∀ i, Measurable (s i)) (h : Y → ℝ≥0∞) (hh : Measurable h) (p : P) :
    (∫⁻ y, h y ∂atomicVisitKernel q hq s hs p) = ∑' i, q i p*h (s i p) := by
  change (∫⁻ y, h y ∂Measure.sum (fun i => q i p • Measure.dirac (s i p))) = _
  rw [lintegral_sum_measure]
  simp_rw [lintegral_smul_measure,smul_eq_mul,lintegral_dirac' _ hh]

lemma atomicVisitKernel_finite (q : I → P → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    (s : I → P → Y) (hs : ∀ i, Measurable (s i)) (hb : ∀ p, (∑' i, q i p) ≤ 1) :
    IsFiniteKernel (atomicVisitKernel q hq s hs) := by
  refine ⟨1,ENNReal.one_lt_top,fun p => ?_⟩
  change Measure.sum (fun i => q i p • Measure.dirac (s i p)) univ ≤ 1
  simpa [Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply] using hb p

lemma atomicVisitLaw_lintegral (q : I → P → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    (s : I → P → Y) (hs : ∀ i, Measurable (s i)) (μ : Measure P)
    (h : Y → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ y, h y ∂(atomicVisitKernel q hq s hs ∘ₘ μ)) = ∫⁻ p, ∑' i, q i p*h (s i p) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply,Kernel.lintegral_comp _ _ _ hh]
  simp_rw [atomicVisitKernel_lintegral q hq s hs h hh,Kernel.const_apply]

end

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedTiltedProbability_mass_le (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) :
    (∑' l, indexedTiltedProbability step n F p l) ≤ 1 := by
  simp only [indexedTiltedProbability,ENNReal.tsum_mul_left]
  exact ENNReal.inv_mul_le_one _

omit [Nonempty S] in
lemma indexedTiltedProbability_fixed_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (x : X) (l : IndexedLeaf n) :
    Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n =>
      indexedTiltedProbability step n F (x,p) l) := by
  have hm : Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n => ((x,p),l)) :=
    (measurable_const.prodMk measurable_id).prodMk measurable_const
  have hc := (indexedTiltedProbability_measurable hs n F hF).comp hm
  dsimp only [Function.comp_def, Function.uncurry_def] at hc
  exact hc

omit [Nonempty S] in
lemma indexedLeafState_fixed_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (x : X) (l : IndexedLeaf n) :
    Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n =>
      indexedLeafState step n (x,p.2) l) := by
  have hm : Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n => ((x,p.2),l)) :=
    (measurable_const.prodMk measurable_snd).prodMk measurable_const
  exact (indexedLeafState_measurable hs n).comp hm

def indexedOneStateKernel (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) :
    Kernel (IndexedCascadeBase n×IndexedCascadeMarks S n) X :=
  atomicVisitKernel (I := IndexedLeaf n)
    (P := IndexedCascadeBase n×IndexedCascadeMarks S n) (Y := X)
    (fun l p => indexedTiltedProbability step n F (x,p) l)
    (indexedTiltedProbability_fixed_measurable step hs n F hF x)
    (fun l p => indexedLeafState step n (x,p.2) l)
    (indexedLeafState_fixed_measurable step hs n x)

omit [Nonempty S] in
instance indexedOneStateKernel_finite (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) :
    IsFiniteKernel (indexedOneStateKernel step hs n F hF x) :=
  atomicVisitKernel_finite _ _ _ _ (fun p => indexedTiltedProbability_mass_le step n F (x,p))

omit [Nonempty S] in
lemma indexedOneStateKernel_lintegral (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X)
    (h : X → ℝ≥0∞) (hh : Measurable h) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    (∫⁻ y, h y ∂indexedOneStateKernel step hs n F hF x p) = indexedOneVisit step n F h (x,p) :=
  atomicVisitKernel_lintegral _ _ _ _ h hh p

lemma indexedOneStateLaw_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    indexedOneStateKernel step hs n F hF x ∘ₘ
      ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      pathOneKernel n (fun i => tiltedStateStep ν step (z i) (F i)) x := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [Measure.comp_eq_comp_const_apply,Kernel.lintegral_comp _ _ _ hh]
  simp_rw [indexedOneStateKernel_lintegral step hs n F hF x h hh,Kernel.const_apply]
  rw [indexedOneVisit_integral ν step hs n z hz hz0 hz1 F hF hI hM h hh x,
    pathOneKernel_lintegral ν step hs n z F hF hI hM h hh x]

end SphericalPerceptronFreeEnergy
end

end OAI
