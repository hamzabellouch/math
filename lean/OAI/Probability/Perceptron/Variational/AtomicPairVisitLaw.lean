import Mathlib
import OAI.Probability.Perceptron.Variational.TiltedVisitKernelLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedPairStateWeight (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (x : X) (d : Fin (n+1)) (a : IndexedLeaf n×IndexedLeaf n)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n) : ℝ≥0∞ :=
  if indexedCommonDepth n a.1 a.2=d then
    indexedTiltedProbability step n F (x,p) a.1*indexedTiltedProbability step n F (x,p) a.2 else 0

omit [Nonempty S] in
lemma indexedPairStateWeight_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (x : X) (d : Fin (n+1)) (a : IndexedLeaf n×IndexedLeaf n) :
    Measurable (indexedPairStateWeight step n F x d a) := by
  unfold indexedPairStateWeight
  split_ifs
  · exact (indexedTiltedProbability_fixed_measurable step hs n F hF x a.1).mul
      (indexedTiltedProbability_fixed_measurable step hs n F hF x a.2)
  · exact measurable_const

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedPairStateWeight_mass_le (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (x : X) (d : Fin (n+1)) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    (∑' a, indexedPairStateWeight step n F x d a p) ≤ 1 := by
  calc
    _ ≤ ∑' a : IndexedLeaf n×IndexedLeaf n,
        indexedTiltedProbability step n F (x,p) a.1*indexedTiltedProbability step n F (x,p) a.2 :=
      ENNReal.tsum_le_tsum (fun a => by unfold indexedPairStateWeight; split_ifs <;> simp)
    _ = (∑' l, indexedTiltedProbability step n F (x,p) l)*
        (∑' l, indexedTiltedProbability step n F (x,p) l) := by
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right]
    _ ≤ 1*1 := mul_le_mul' (indexedTiltedProbability_mass_le step n F (x,p))
      (indexedTiltedProbability_mass_le step n F (x,p))
    _ = 1 := one_mul _

def indexedPairStateKernel (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) (d : Fin (n+1)) :
    Kernel (IndexedCascadeBase n×IndexedCascadeMarks S n) (X×X) :=
  atomicVisitKernel (I := IndexedLeaf n×IndexedLeaf n)
    (P := IndexedCascadeBase n×IndexedCascadeMarks S n) (Y := X×X)
    (indexedPairStateWeight step n F x d) (indexedPairStateWeight_measurable step hs n F hF x d)
    (fun a p => (indexedLeafState step n (x,p.2) a.1,indexedLeafState step n (x,p.2) a.2))
    (fun a => (indexedLeafState_fixed_measurable step hs n x a.1).prodMk
      (indexedLeafState_fixed_measurable step hs n x a.2))

instance indexedPairStateKernel_finite (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) (d : Fin (n+1)) :
    IsFiniteKernel (indexedPairStateKernel step hs n F hF x d) :=
  atomicVisitKernel_finite _ _ _ _ (indexedPairStateWeight_mass_le step n F x d)

omit [Nonempty S] in
lemma indexedPairStateKernel_lintegral (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) (d : Fin (n+1))
    (h k : X → ℝ≥0∞) (hh : Measurable h) (hk : Measurable k)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    (∫⁻ y, h y.1*k y.2 ∂indexedPairStateKernel step hs n F hF x d p) =
      indexedTwoVisit step n F h k d (x,p) := by
  rw [indexedPairStateKernel,atomicVisitKernel_lintegral _ _ _ _ _
    (show Measurable (fun y : X×X => h y.1*k y.2) from
      (hh.comp measurable_fst).mul (hk.comp measurable_snd)),ENNReal.tsum_prod']
  unfold indexedTwoVisit
  apply tsum_congr
  intro l
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro m
  simp only [indexedPairStateWeight]
  split_ifs <;> simp [mul_assoc]

omit [MeasurableSpace X] in
lemma oneDecoratedVisit_bare_eq {Y : Type} (h : X → ℝ≥0∞) (k : Y → ℝ≥0∞) (n : ℕ) :
    (oneDecoratedVisit h n).bare n = (oneDecoratedVisit k n).bare n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [oneDecoratedVisit,DecoratedVisitShape.bare] using ih

omit [MeasurableSpace X] in
lemma twoDecoratedVisit_bare_eq {Y : Type} (h k : X → ℝ≥0∞) (h' k' : Y → ℝ≥0∞)
    (n : ℕ) (d : Fin (n+1)) :
    (twoDecoratedVisit h k n d).bare n = (twoDecoratedVisit h' k' n d).bare n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction d using Fin.cases with
    | zero => simp [twoDecoratedVisit,DecoratedVisitShape.bare,oneDecoratedVisit_bare_eq h h',
        oneDecoratedVisit_bare_eq k k']
    | succ d => simpa [twoDecoratedVisit,DecoratedVisitShape.bare] using ih d

def twoVisitMass (n : ℕ) (z : Fin n → ℝ) (d : Fin (n+1)) : ℝ≥0∞ :=
  cascadeShapeLikelihood n z 0 ((twoDecoratedVisit (X := Unit) (fun _ => 1) (fun _ => 1) n d).bare n)

omit [MeasurableSpace X] in
lemma twoVisitMass_eq (n : ℕ) (z : Fin n → ℝ) (d : Fin (n+1)) (h k : X → ℝ≥0∞) :
    twoVisitMass n z d = cascadeShapeLikelihood n z 0 ((twoDecoratedVisit h k n d).bare n) := by
  unfold twoVisitMass
  rw [twoDecoratedVisit_bare_eq (fun _ : Unit => 1) (fun _ => 1) h k]

end
section
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

lemma lintegral_indicator_prod (μ : Measure (X×Y)) (s : Set X) (t : Set Y)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (∫⁻ p, s.indicator (fun _ => (1 : ℝ≥0∞)) p.1*t.indicator (fun _ => (1 : ℝ≥0∞)) p.2 ∂μ) =
      μ (s×ˢt) := by
  rw [← lintegral_indicator_one (hs.prod ht)]
  congr 1
  funext p
  by_cases h : p.1∈s <;> by_cases k : p.2∈t <;> simp [h,k]

end
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma indexedPairStateLaw_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (d : Fin (n+1)) :
    indexedPairStateKernel step hs n F hF x d ∘ₘ
      ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      twoVisitMass n z d • pathPairKernel n (fun i => tiltedStateStep ν step (z i) (F i)) d x := by
  apply Measure.ext_prod
  intro s t hs' ht'
  let h := s.indicator (fun _ => (1 : ℝ≥0∞))
  let k := t.indicator (fun _ => (1 : ℝ≥0∞))
  have hh : Measurable h := measurable_const.indicator hs'
  have hk : Measurable k := measurable_const.indicator ht'
  rw [← lintegral_indicator_prod _ s t hs' ht',← lintegral_indicator_prod _ s t hs' ht']
  change (∫⁻ p : X×X, h p.1*k p.2 ∂_) = ∫⁻ p : X×X, h p.1*k p.2 ∂_
  rw [Measure.comp_eq_comp_const_apply,Kernel.lintegral_comp _ _ _
    (show Measurable (fun p : X×X => h p.1*k p.2) from
      (hh.comp measurable_fst).mul (hk.comp measurable_snd))]
  simp_rw [indexedPairStateKernel_lintegral step hs n F hF x d h k hh hk,Kernel.const_apply]
  rw [indexedTwoVisit_integral ν step hs n z hz hz0 hz1 F hF hI hM h k hh hk d x,
    lintegral_smul_measure,smul_eq_mul,
    pathPairKernel_lintegral ν step hs n z F hF hI hM h k hh hk d x,
    twoVisitMass_eq n z d h k]

end SphericalPerceptronFreeEnergy
end

end OAI
