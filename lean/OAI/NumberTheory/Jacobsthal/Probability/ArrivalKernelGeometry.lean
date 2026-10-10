import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.WithDensity
import OAI.NumberTheory.Jacobsthal.Estimates.EvenInverseBands

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelWeightTransform

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

structure PositiveWeight (α : Type*) [MeasurableSpace α] where
  value : α → ℝ≥0∞
  measurable_value : Measurable value
  ne_zero : ∀ a, value a ≠ 0
  ne_top : ∀ a, value a ≠ ∞

instance : CoeFun (PositiveWeight α) (fun _ => α → ℝ≥0∞) := ⟨PositiveWeight.value⟩

theorem ratio_measurable (w : PositiveWeight α) :
    Measurable (Function.uncurry (fun a b => w b / w a)) :=
  (w.measurable_value.comp measurable_snd).div (w.measurable_value.comp measurable_fst)

theorem ratio_ne_top (w : PositiveWeight α) (a b : α) : w b / w a ≠ ∞ :=
  ENNReal.div_ne_top (w.ne_top b) (w.ne_zero a)

theorem ratio_cocycle (w : PositiveWeight α) (a b c : α) :
    (w b / w a) * (w c / w b) = w c / w a := by
  simp only [div_eq_mul_inv]
  calc
    _ = (w b * (w b)⁻¹) * (w c * (w a)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (w.ne_zero b) (w.ne_top b), one_mul]

noncomputable def conjugate (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) : Kernel α α :=
  K.withDensity (fun a b => w b / w a)

instance conjugate_isSFiniteKernel (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) :
    IsSFiniteKernel (conjugate K w) := Kernel.IsSFiniteKernel.withDensity K (ratio_ne_top w)

instance kernelPower_isSFiniteKernel (K : Kernel α α) [IsSFiniteKernel K] (n : ℕ) :
    IsSFiniteKernel (K ^ n) := by
  induction n with
  | zero => change IsSFiniteKernel (Kernel.id : Kernel α α); infer_instance
  | succ n ih =>
    have hp : K ^ (n + 1) = K ∘ₖ (K ^ n) := pow_succ' _ _
    rw [hp]
    infer_instance

theorem conjugate_apply (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) (a : α) :
    conjugate K w a = (K a).withDensity (fun b => w b / w a) :=
  Kernel.withDensity_apply K (ratio_measurable w) a

theorem conjugate_lintegral (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) (a : α)
    {F : α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ b, F b ∂conjugate K w a) = ∫⁻ b, (w b / w a) * F b ∂K a :=
  Kernel.lintegral_withDensity K (ratio_measurable w) a hF

theorem conjugate_id (w : PositiveWeight α) : conjugate (Kernel.id : Kernel α α) w = Kernel.id := by
  ext a : 1
  apply Measure.ext_of_lintegral
  intro F hF
  rw [conjugate_lintegral _ w a hF,
    Kernel.lintegral_id' (f := fun b => (w b / w a) * F b) ((w.measurable_value.div measurable_const).mul hF),
    ENNReal.div_self (w.ne_zero a) (w.ne_top a), one_mul, Kernel.lintegral_id' hF]

theorem conjugate_comp (L K : Kernel α α) [IsSFiniteKernel L] [IsSFiniteKernel K]
    (w : PositiveWeight α) :
    (conjugate L w) ∘ₖ (conjugate K w) = conjugate (L ∘ₖ K) w := by
  ext a : 1
  apply Measure.ext_of_lintegral
  intro F hF
  have hInner : Measurable (fun b => ∫⁻ c, F c ∂conjugate L w b) := hF.lintegral_kernel
  have hWeighted : Measurable (fun c => (w c / w a) * F c) :=
    (w.measurable_value.div measurable_const).mul hF
  rw [Kernel.lintegral_comp _ _ _ hF,
    conjugate_lintegral K w a (F := fun b => ∫⁻ c, F c ∂conjugate L w b) hInner,
    conjugate_lintegral (L ∘ₖ K) w a hF,
    Kernel.lintegral_comp L K a hWeighted]
  apply lintegral_congr
  intro b
  rw [conjugate_lintegral L w b hF,
    ← lintegral_const_mul' _ _ (ratio_ne_top w a b)]
  apply lintegral_congr
  intro c
  rw [← mul_assoc, ratio_cocycle]

theorem conjugate_congr (L K : Kernel α α) [IsSFiniteKernel L] [IsSFiniteKernel K]
    (h : L = K) (w : PositiveWeight α) : conjugate L w = conjugate K w := by
  subst K
  rfl

theorem conjugate_pow (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) (n : ℕ) :
    (conjugate K w) ^ n = conjugate (K ^ n) w := by
  induction n with
  | zero =>
    change (Kernel.id : Kernel α α) = conjugate Kernel.id w
    exact (conjugate_id w).symm
  | succ n ih =>
    have hp : (conjugate K w) ^ (n + 1) = (conjugate K w) ∘ₖ ((conjugate K w) ^ n) := pow_succ' _ _
    have hq : K ^ (n + 1) = K ∘ₖ (K ^ n) := pow_succ' _ _
    rw [hp, ih, conjugate_comp]
    exact conjugate_congr (K ∘ₖ (K ^ n)) (K ^ (n + 1)) hq.symm w

theorem conjugate_pow_lintegral (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α)
    (n : ℕ) (a : α) {F : α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ b, F b ∂((conjugate K w) ^ n) a) =
      (w a)⁻¹ * ∫⁻ b, w b * F b ∂(K ^ n) a := by
  rw [conjugate_pow, conjugate_lintegral _ w a hF]
  calc
    _ = ∫⁻ b, (w a)⁻¹ * (w b * F b) ∂(K ^ n) a := by
      apply lintegral_congr
      intro b
      rw [div_eq_mul_inv]
      ring
    _ = _ := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (w.ne_zero a))

theorem conjugate_prefix_sum (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) :
    Kernel.sum (fun n : ℕ => (conjugate K w) ^ n) =
      conjugate (Kernel.sum (fun n : ℕ => K ^ n)) w := by
  calc
    _ = Kernel.sum (fun n : ℕ => conjugate (K ^ n) w) := by
      apply congrArg Kernel.sum
      funext n
      exact conjugate_pow K w n
    _ = _ := (Kernel.withDensity_kernel_sum (fun n : ℕ => K ^ n) (fun _ => inferInstance)
      (fun a b => w b / w a)).symm

end NumberTheoryLean.KernelWeightTransform

end

section

namespace NumberTheoryLean.KernelExitBarrier

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelWeightTransform

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem restrict_inner_comp (K : Kernel α β) (L : Kernel γ α) {A : Set α} (hA : MeasurableSet A)
    (hzero : ∀ a ∉ A, K a = 0) : K ∘ₖ (L.restrict hA) = K ∘ₖ L := by
  classical
  ext z B hB
  rw [Kernel.comp_apply' _ _ _ hB, Kernel.comp_apply' _ _ _ hB, Kernel.restrict_apply,
    ← lintegral_indicator hA]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ A
  · rw [indicator_of_mem ha]
  · rw [indicator_of_notMem ha, hzero a ha]
    simp

theorem restricted_pow_eq (K : Kernel α α) {A : Set α} (hA : MeasurableSet A)
    (hNoReturn : ∀ a ∉ A, K a A = 0) (n : ℕ) :
    (K.restrict hA) ^ (n + 1) = (K ^ (n + 1)).restrict hA := by
  have hz : ∀ a ∉ A, K.restrict hA a = 0 := by
    intro a ha
    rw [Kernel.restrict_apply]
    exact Measure.restrict_eq_zero.mpr (hNoReturn a ha)
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : (K.restrict hA) ^ (n + 1 + 1) = (K.restrict hA) ∘ₖ ((K.restrict hA) ^ (n + 1)) := pow_succ' _ _
    have hR : K ^ (n + 1 + 1) = K ∘ₖ (K ^ (n + 1)) := pow_succ' _ _
    rw [hL, ih, restrict_inner_comp (K.restrict hA) (K ^ (n + 1)) hA hz,
      Kernel.comp_restrict hA, hR]

theorem restricted_future_sum (K : Kernel α α) {A : Set α} (hA : MeasurableSet A)
    (hNoReturn : ∀ a ∉ A, K a A = 0) :
    Kernel.sum (fun n : ℕ => (K.restrict hA) ^ (n + 1)) =
      (Kernel.sum (fun n : ℕ => K ^ (n + 1))).restrict hA := by
  ext z B hB
  rw [Kernel.sum_apply' _ _ hB, Kernel.restrict_apply' _ _ _ hB,
    Kernel.sum_apply' _ _ (hB.inter hA)]
  apply tsum_congr
  intro n
  rw [restricted_pow_eq K hA hNoReturn, Kernel.restrict_apply' _ _ _ hB]

theorem conjugate_restrict (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α)
    {A : Set α} (hA : MeasurableSet A) :
    (conjugate K w).restrict hA = conjugate (K.restrict hA) w := by
  ext a : 1
  rw [Kernel.restrict_apply, conjugate_apply K w a, conjugate_apply (K.restrict hA) w a,
    Kernel.restrict_apply, MeasureTheory.restrict_withDensity hA]

end NumberTheoryLean.KernelExitBarrier

end

section

namespace NumberTheoryLean.KernelMappedDomination

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelWeightTransform

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem mapped_pow_lintegral_le (K : Kernel α α) (L : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel L] (P : α → β) (hP : Measurable P)
    (hrow : ∀ x, (K x).map P ≤ L (P x)) :
    ∀ n : ℕ, ∀ x : α, ∀ f : β → ℝ≥0∞, Measurable f →
      (∫⁻ y, f (P y) ∂(K^n) x) ≤ ∫⁻ y, f y ∂(L^n) (P x) := by
  intro n
  induction n with
  | zero =>
    intro x f hf
    change (∫⁻ y, f (P y) ∂Measure.dirac x) ≤ ∫⁻ y, f y ∂Measure.dirac (P x)
    rw [lintegral_dirac' _ (f := fun y => f (P y)) (hf.comp hP), lintegral_dirac' _ hf]
  | succ n ih =>
    intro x f hf
    have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    have hq : L^(n+1) = (L^n) ∘ₖ L := pow_succ _ _
    rw [hp, hq,
      Kernel.lintegral_comp _ _ _ (g := fun y => f (P y)) (hf.comp hP),
      Kernel.lintegral_comp _ _ _ hf]
    have hF : Measurable (fun y => ∫⁻ t, f t ∂(L^n) y) := hf.lintegral_kernel
    calc
      _ ≤ ∫⁻ y, ∫⁻ t, f t ∂(L^n) (P y) ∂K x := lintegral_mono (fun y => ih y f hf)
      _ = ∫⁻ y, ∫⁻ t, f t ∂(L^n) y ∂(K x).map P :=
        (lintegral_map (f := fun y => ∫⁻ t, f t ∂(L^n) y) hF hP).symm
      _ ≤ _ := lintegral_mono' (hrow x) le_rfl

theorem mapped_pow_le (K : Kernel α α) (L : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel L] (P : α → β) (hP : Measurable P)
    (hrow : ∀ x, (K x).map P ≤ L (P x)) (n : ℕ) (x : α) :
    ((K^n) x).map P ≤ (L^n) (P x) := by
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (fun _ : β => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have h := mapped_pow_lintegral_le K L P hP hrow n x _ hf
  rw [← lintegral_map (f := A.indicator (fun _ : β => (1 : ℝ≥0∞))) hf hP] at h
  simpa only [lintegral_indicator hA, lintegral_const, one_mul, Measure.restrict_apply_univ] using h

theorem mapped_prefix_sum_le (K : Kernel α α) (L : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel L] (P : α → β) (hP : Measurable P)
    (hrow : ∀ x, (K x).map P ≤ L (P x)) (x : α)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (∑' n : ℕ, ∫⁻ y, f (P y) ∂(K^n) x) ≤
      ∑' n : ℕ, ∫⁻ y, f y ∂(L^n) (P x) :=
  ENNReal.tsum_le_tsum (fun n => mapped_pow_lintegral_le K L P hP hrow n x f hf)

theorem mapped_pow_lintegral_eq (K : Kernel α α) (L : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel L] (P : α → β) (hP : Measurable P)
    (hrow : ∀ x, (K x).map P = L (P x)) :
    ∀ n : ℕ, ∀ x : α, ∀ f : β → ℝ≥0∞, Measurable f →
      (∫⁻ y, f (P y) ∂(K^n) x) = ∫⁻ y, f y ∂(L^n) (P x) := by
  intro n
  induction n with
  | zero =>
    intro x f hf
    change (∫⁻ y, f (P y) ∂Measure.dirac x) = ∫⁻ y, f y ∂Measure.dirac (P x)
    rw [lintegral_dirac' _ (f := fun y => f (P y)) (hf.comp hP), lintegral_dirac' _ hf]
  | succ n ih =>
    intro x f hf
    have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    have hq : L^(n+1) = (L^n) ∘ₖ L := pow_succ _ _
    rw [hp, hq, Kernel.lintegral_comp _ _ _ (g := fun y => f (P y)) (hf.comp hP),
      Kernel.lintegral_comp _ _ _ hf]
    have hF : Measurable (fun y => ∫⁻ t, f t ∂(L^n) y) := hf.lintegral_kernel
    calc
      _ = ∫⁻ y, ∫⁻ t, f t ∂(L^n) (P y) ∂K x := lintegral_congr (fun y => ih y f hf)
      _ = ∫⁻ y, ∫⁻ t, f t ∂(L^n) y ∂(K x).map P :=
        (lintegral_map (f := fun y => ∫⁻ t, f t ∂(L^n) y) hF hP).symm
      _ = _ := by rw [hrow x]

theorem mapped_pow_eq (K : Kernel α α) (L : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel L] (P : α → β) (hP : Measurable P)
    (hrow : ∀ x, (K x).map P = L (P x)) (n : ℕ) (x : α) :
    ((K^n) x).map P = (L^n) (P x) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hP]
  exact mapped_pow_lintegral_eq K L P hP hrow n x f hf

end NumberTheoryLean.KernelMappedDomination

end

section

namespace NumberTheoryLean.HarmonicWeightKernel

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open DerivativeWeights WeightFutureIntegrals TransitionKernels FinitePathGeometry
open FinitePathMeasures OccupationBoundaries InvariantInverseWeights
open KernelWeightTransform CostPrefixTransport OccupationDecomposition

noncomputable def harmonicWeight : PositiveWeight CostState where
  value z := ENNReal.ofReal (Real.exp (-2 * z.2) / stateWeight z.1)
  measurable_value := ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).div
      (stateWeight_measurable.comp measurable_fst))
  ne_zero z := (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) (stateWeight_pos z.1))).ne'
  ne_top _ := ENNReal.ofReal_ne_top

noncomputable def harmonicKernel : Kernel CostState CostState := conjugate costKernel harmonicWeight

instance harmonicKernel_isSFiniteKernel : IsSFiniteKernel harmonicKernel := by unfold harmonicKernel; infer_instance

theorem exp_neg_two_cost {t : ℝ} (ht : 0 < t) :
    Real.exp (-2 * cost t) = (t / (t + 1)) ^ 2 := by
  have h : Real.exp (-cost t) = t / (t + 1) := by
    simpa only [nextGap, one_mul] using (nextGap_eq_cost (r := 1) ht).symm
  calc
    _ = Real.exp (-cost t + -cost t) := congrArg Real.exp (by ring)
    _ = Real.exp (-cost t) * Real.exp (-cost t) := Real.exp_add _ _
    _ = _ := by rw [h, pow_two]

theorem transition_weight_ratio (z : CostState) (s : State) :
    harmonicWeight (s, z.2 + cost (stateRatio s)) / harmonicWeight z =
      ENNReal.ofReal ((stateRatio s / (stateRatio s + 1)) ^ 2 *
        (stateWeight z.1 / stateWeight s)) := by
  have hz : 0 < Real.exp (-2 * z.2) / stateWeight z.1 := div_pos (Real.exp_pos _) (stateWeight_pos z.1)
  change ENNReal.ofReal (Real.exp (-2 * (z.2 + cost (stateRatio s))) / stateWeight s) /
    ENNReal.ofReal (Real.exp (-2 * z.2) / stateWeight z.1) = _
  rw [← ENNReal.ofReal_div_of_pos hz]
  congr 1
  rw [show -2 * (z.2 + cost (stateRatio s)) = (-2 * z.2) + (-2 * cost (stateRatio s)) by ring,
    Real.exp_add, exp_neg_two_cost (stateRatio_pos s)]
  field_simp [(stateWeight_pos z.1).ne', (stateWeight_pos s).ne', (Real.exp_pos (-2 * z.2)).ne']

noncomputable def correction (i : Side) (s t : ℝ) : ℝ :=
  (t / (t + 1)) ^ 2 * (weight i s / weight i.flip t)

theorem weight_measurable (i : Side) : Measurable (weight i) := by
  cases i
  · exact phiEven_measurable
  · exact phiOdd_continuous.measurable

theorem correction_measurable (i : Side) (s : ℝ) : Measurable (correction i s) :=
  ((measurable_id.div (measurable_id.add measurable_const)).pow_const 2).mul
    (measurable_const.div (weight_measurable i.flip))

noncomputable def harmonicRatioDensity (i : Side) (s : ℝ) : ℝ → ℝ≥0∞ :=
  (Ici (minRatio i s)).indicator (fun t => ENNReal.ofReal (1 / (t + 1)))

theorem harmonicRatioDensity_measurable (i : Side) (s : ℝ) : Measurable (harmonicRatioDensity i s) :=
  (ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.add measurable_const))).indicator measurableSet_Ici

theorem corrected_density_eq {i : Side} {s : ℝ} (hs : Valid i s) (t : ℝ) :
    ENNReal.ofReal (transitionDensity i s t) * ENNReal.ofReal (correction i s t) =
      harmonicRatioDensity i s t := by
  by_cases ht : minRatio i s ≤ t
  · have hv := valid_next hs ht
    have hp : 0 ≤ transitionDensity i s t := by
      unfold transitionDensity tailDensity
      rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
      exact div_nonneg (mul_nonneg (W_pos (valid_pos hv)).le (weight_pos hv).le) (weight_pos hs).le
    rw [← ENNReal.ofReal_mul hp, harmonicRatioDensity,
      indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
    congr 1
    have he := step_weight_identity (r := 1) hs ht (by norm_num)
    simpa only [correction, nextGap, one_mul, div_one, mul_assoc] using he.symm
  · rw [transitionDensity, tailDensity, indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht),
      ENNReal.ofReal_zero, zero_mul, harmonicRatioDensity,
      indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht)]

theorem initial_weight_inv (s : State) : (harmonicWeight (s, 0))⁻¹ = ENNReal.ofReal (stateWeight s) := by
  change (ENNReal.ofReal (Real.exp (-2 * (0 : ℝ)) / stateWeight s))⁻¹ = _
  rw [mul_zero, Real.exp_zero, ENNReal.ofReal_div_of_pos (stateWeight_pos s), ENNReal.ofReal_one, one_div, inv_inv]

theorem harmonic_prefix_lintegral (n : ℕ) (s : State) {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(harmonicKernel ^ n) (s, 0)) = ENNReal.ofReal (stateWeight s) *
      ∫⁻ z, ENNReal.ofReal (Real.exp (-2 * z.2) / stateWeight z.1) * F z ∂(costKernel ^ n) (s, 0) := by
  rw [harmonicKernel, conjugate_pow_lintegral costKernel harmonicWeight n (s, 0) hF, initial_weight_inv]
  rfl

noncomputable def harmonicOccupation : Kernel CostState CostState := Kernel.sum (fun n : ℕ => harmonicKernel ^ n)

instance harmonicOccupation_isSFiniteKernel : IsSFiniteKernel harmonicOccupation := by
  unfold harmonicOccupation
  infer_instance

theorem inclusiveOccupation_eq_prefix_sum : inclusiveOccupation = Kernel.sum (fun n : ℕ => costKernel ^ n) := by
  ext z B hB
  rw [inclusiveOccupation, _root_.add_apply, Measure.add_apply, fullOccupation,
    Kernel.sum_apply' _ _ hB, Kernel.sum_apply' _ _ hB]
  exact (tsum_eq_zero_add' (f := fun n : ℕ => (costKernel ^ n) z B) ENNReal.summable).symm

theorem harmonicOccupation_transform : harmonicOccupation = conjugate inclusiveOccupation harmonicWeight := by
  rw [harmonicOccupation, harmonicKernel, conjugate_prefix_sum]
  exact conjugate_congr _ _ inclusiveOccupation_eq_prefix_sum.symm harmonicWeight

end NumberTheoryLean.HarmonicWeightKernel

end

section

namespace NumberTheoryLean.HarmonicKernelDensities

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open KernelDensityBridge InvariantInverseWeights KernelWeightTransform HarmonicWeightKernel
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

theorem harmonic_even_typed (s : EvenState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inl s, T)) =
      ∫⁻ t : OddState, ENNReal.ofReal (correction .even s.1 t.1) * H (.inr t, T + cost t.1) ∂evenToOdd s := by
  have hm : Measurable (fun y : CostState => (harmonicWeight y / harmonicWeight (.inl s, T)) * H y) :=
    (harmonicWeight.measurable_value.div measurable_const).mul hH
  rw [harmonicKernel, conjugate_lintegral costKernel harmonicWeight (.inl s, T) hH,
    costKernel_even_lintegral s T (H := fun y : CostState => (harmonicWeight y / harmonicWeight (.inl s, T)) * H y) hm]
  apply lintegral_congr
  intro t
  have hr : harmonicWeight (.inr t, T + cost t.1) / harmonicWeight (.inl s, T) =
      ENNReal.ofReal (correction .even s.1 t.1) := by
    simpa only [stateRatio, stateWeight, weight, Side.flip, correction, Sum.elim_inl, Sum.elim_inr] using
      transition_weight_ratio (.inl s, T) (.inr t)
  exact congrArg (fun c : ℝ≥0∞ => c * H (.inr t, T + cost t.1)) hr

theorem harmonic_odd_typed (s : OddState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inr s, T)) =
      ∫⁻ t : EvenState, ENNReal.ofReal (correction .odd s.1 t.1) * H (.inl t, T + cost t.1) ∂oddToEven s := by
  have hm : Measurable (fun y : CostState => (harmonicWeight y / harmonicWeight (.inr s, T)) * H y) :=
    (harmonicWeight.measurable_value.div measurable_const).mul hH
  rw [harmonicKernel, conjugate_lintegral costKernel harmonicWeight (.inr s, T) hH,
    costKernel_odd_lintegral s T (H := fun y : CostState => (harmonicWeight y / harmonicWeight (.inr s, T)) * H y) hm]
  apply lintegral_congr
  intro t
  have hr : harmonicWeight (.inl t, T + cost t.1) / harmonicWeight (.inr s, T) =
      ENNReal.ofReal (correction .odd s.1 t.1) := by
    simpa only [stateRatio, stateWeight, weight, Side.flip, correction, Sum.elim_inl, Sum.elim_inr] using
      transition_weight_ratio (.inr s, T) (.inl t)
  exact congrArg (fun c : ℝ≥0∞ => c * H (.inl t, T + cost t.1)) hr

noncomputable def evenUpdateReal (T t : ℝ) : CostState := (.inr (oddLift t), T + cost t)
noncomputable def oddUpdateReal (T t : ℝ) : CostState := (.inl (evenLift t), T + cost t)

theorem evenUpdateReal_measurable (T : ℝ) : Measurable (evenUpdateReal T) :=
  (measurable_inr.comp oddLift_measurable).prodMk (measurable_const.add cost_measurable)

theorem oddUpdateReal_measurable (T : ℝ) : Measurable (oddUpdateReal T) :=
  (measurable_inl.comp evenLift_measurable).prodMk (measurable_const.add cost_measurable)

theorem harmonic_even_joint_lintegral (s : EvenState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inl s, T)) =
      ∫⁻ t : ℝ, harmonicRatioDensity .even s.1 t * H (evenUpdateReal T t) := by
  let G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (correction .even s.1 t) * H (evenUpdateReal T t)
  have hG : Measurable G := (ENNReal.measurable_ofReal.comp (correction_measurable .even s.1)).mul
    (hH.comp (evenUpdateReal_measurable T))
  rw [harmonic_even_typed s T hH]
  calc
    _ = ∫⁻ t : OddState, G t.1 ∂evenToOdd s := by
      apply lintegral_congr
      intro t
      simp only [G, evenUpdateReal, oddLift_ratio]
    _ = ∫⁻ t : ℝ, G t ∂evenKernel s := evenToOdd_lintegral_ratio s hG
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity .even s.1 t) * G t := evenKernel_lintegral_density s hG
    _ = _ := by
      apply lintegral_congr
      intro t
      dsimp [G]
      rw [← mul_assoc, corrected_density_eq (i := .even) (s := s.1) s.2 t]

theorem harmonic_odd_joint_lintegral (s : OddState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inr s, T)) =
      ∫⁻ t : ℝ, harmonicRatioDensity .odd s.1 t * H (oddUpdateReal T t) := by
  let G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (correction .odd s.1 t) * H (oddUpdateReal T t)
  have hG : Measurable G := (ENNReal.measurable_ofReal.comp (correction_measurable .odd s.1)).mul
    (hH.comp (oddUpdateReal_measurable T))
  rw [harmonic_odd_typed s T hH]
  calc
    _ = ∫⁻ t : EvenState, G t.1 ∂oddToEven s := by
      apply lintegral_congr
      intro t
      simp only [G, oddUpdateReal, evenLift_ratio]
    _ = ∫⁻ t : ℝ, G t ∂oddKernel s := oddToEven_lintegral_ratio s hG
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity .odd s.1 t) * G t := oddKernel_lintegral_density s hG
    _ = _ := by
      apply lintegral_congr
      intro t
      dsimp [G]
      rw [← mul_assoc, corrected_density_eq (i := .odd) (s := s.1) s.2 t]

theorem harmonic_even_measure (s : EvenState) (T : ℝ) :
    harmonicKernel (.inl s, T) =
      (volume.withDensity (harmonicRatioDensity .even s.1)).map (evenUpdateReal T) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [harmonic_even_joint_lintegral s T hH,
    lintegral_map hH (evenUpdateReal_measurable T),
    lintegral_withDensity_eq_lintegral_mul volume (f := harmonicRatioDensity .even s.1)
      (g := fun t => H (evenUpdateReal T t)) (harmonicRatioDensity_measurable .even s.1)
      (hH.comp (evenUpdateReal_measurable T))]
  rfl

theorem harmonic_odd_measure (s : OddState) (T : ℝ) :
    harmonicKernel (.inr s, T) =
      (volume.withDensity (harmonicRatioDensity .odd s.1)).map (oddUpdateReal T) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [harmonic_odd_joint_lintegral s T hH,
    lintegral_map hH (oddUpdateReal_measurable T),
    lintegral_withDensity_eq_lintegral_mul volume (f := harmonicRatioDensity .odd s.1)
      (g := fun t => H (oddUpdateReal T t)) (harmonicRatioDensity_measurable .odd s.1)
      (hH.comp (oddUpdateReal_measurable T))]
  rfl

end NumberTheoryLean.HarmonicKernelDensities

end

section

namespace NumberTheoryLean.ArrivalKernelGeometry

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries RegeneratingInverseBands KernelDensityBridge
open HarmonicWeightKernel KernelWeightTransform

noncomputable def currentExponent (v : ℝ) (z : CostState) : ℝ := gapValue v z / stateRatio z.1

theorem gapValue_measurable (v : ℝ) : Measurable (gapValue v) :=
  Real.measurable_exp.comp (measurable_const.sub measurable_snd)

theorem currentExponent_measurable (v : ℝ) : Measurable (currentExponent v) :=
  (gapValue_measurable v).div (stateRatio_measurable.comp measurable_fst)

theorem currentExponent_pos (v : ℝ) (z : CostState) : 0 < currentExponent v z :=
  div_pos (Real.exp_pos _) (stateRatio_pos z.1)

def arrivalSet (v ell : ℝ) : Set CostState := {z | ell < currentExponent v z}

theorem arrivalSet_measurable (v ell : ℝ) : MeasurableSet (arrivalSet v ell) :=
  measurableSet_lt measurable_const (currentExponent_measurable v)

theorem arrivalSet_eq_cutoff (v : ℝ) {ell : ℝ} (hell : 0 < ell) :
    arrivalSet v ell = {z | stateRatio z.1 < gapValue v z / ell} := by
  ext z
  change ell < gapValue v z / stateRatio z.1 ↔ stateRatio z.1 < gapValue v z / ell
  rw [lt_div_iff₀ (stateRatio_pos z.1), lt_div_iff₀ hell, mul_comm ell (stateRatio z.1)]

theorem gapValue_update (v : ℝ) (z : CostState) (s : State) :
    gapValue v (s, z.2 + cost (stateRatio s)) = nextGap (gapValue v z) (stateRatio s) := by
  rw [nextGap_eq_cost (stateRatio_pos s)]
  change Real.exp (v - (z.2 + cost (stateRatio s))) = Real.exp (v - z.2) * Real.exp (-cost (stateRatio s))
  rw [show v - (z.2 + cost (stateRatio s)) = (v - z.2) + (-cost (stateRatio s)) by ring, Real.exp_add]

theorem currentExponent_update (v : ℝ) (z : CostState) (s : State) :
    currentExponent v (s, z.2 + cost (stateRatio s)) = nextExponent (gapValue v z) (stateRatio s) := by
  change gapValue v (s, z.2 + cost (stateRatio s)) / stateRatio s = _
  rw [gapValue_update, nextGap_div_ratio (stateRatio_pos s)]

theorem stateKernel_ae_minRatio (s : State) :
    ∀ᵐ t ∂stateKernel s, minRatio (stateSide s) (stateRatio s) ≤ stateRatio t := by
  cases s with
  | inl s =>
    change ∀ᵐ t ∂stateKernel (.inl s), s.1 - 1 ≤ stateRatio t
    have h : ∀ᵐ u ∂(stateKernel (.inl s)).map stateRatio, s.1 - 1 ≤ u := by
      rw [stateKernel_even_ratio]
      exact evenKernel_ae_support s
    exact (ae_map_iff stateRatio_measurable.aemeasurable measurableSet_Ici).mp h
  | inr s =>
    change ∀ᵐ t ∂stateKernel (.inr s), max 2 (s.1 - 1) ≤ stateRatio t
    have h : ∀ᵐ u ∂(stateKernel (.inr s)).map stateRatio, max 2 (s.1 - 1) ≤ u := by
      rw [stateKernel_odd_ratio]
      exact oddKernel_ae_support s
    exact (ae_map_iff stateRatio_measurable.aemeasurable measurableSet_Ici).mp h

theorem costKernel_gap_flow (v : ℝ) (z : CostState) :
    ∀ᵐ y ∂costKernel z, gapValue v z = gapValue v y + currentExponent v y := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hp : MeasurableSet {y : CostState | gapValue v z = gapValue v y + currentExponent v y} :=
    measurableSet_eq_fun measurable_const ((gapValue_measurable v).add (currentExponent_measurable v))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable hp).mpr
  apply Eventually.of_forall
  intro s
  rw [gapValue_update, currentExponent_update]
  exact (gap_exponent_conservation (stateRatio_pos s)).symm

theorem costKernel_exponent_nonincreasing (v : ℝ) (z : CostState) :
    ∀ᵐ y ∂costKernel z, currentExponent v y ≤ currentExponent v z := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hp : MeasurableSet {y : CostState | currentExponent v y ≤ currentExponent v z} :=
    measurableSet_le (currentExponent_measurable v) measurable_const
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable hp).mpr
  filter_upwards [stateKernel_ae_minRatio z.1] with s hs
  rw [currentExponent_update]
  exact exponent_le_cutoff (stateRatio_valid z.1) hs (Real.exp_pos _)

theorem harmonicKernel_absolutelyContinuous (z : CostState) : harmonicKernel z ≪ costKernel z :=
  Kernel.withDensity_absolutelyContinuous (fun a b => harmonicWeight b / harmonicWeight a) z

theorem harmonicKernel_gap_flow (v : ℝ) (z : CostState) :
    ∀ᵐ y ∂harmonicKernel z, gapValue v z = gapValue v y + currentExponent v y :=
  (harmonicKernel_absolutelyContinuous z).ae_le (costKernel_gap_flow v z)

theorem harmonicKernel_exponent_nonincreasing (v : ℝ) (z : CostState) :
    ∀ᵐ y ∂harmonicKernel z, currentExponent v y ≤ currentExponent v z :=
  (harmonicKernel_absolutelyContinuous z).ae_le (costKernel_exponent_nonincreasing v z)

theorem costKernel_no_reentry (v ell : ℝ) (z : CostState) (hz : z ∉ arrivalSet v ell) :
    costKernel z (arrivalSet v ell) = 0 := by
  have hZ : currentExponent v z ≤ ell := le_of_not_gt hz
  have h : ∀ᵐ y ∂costKernel z, y ∉ arrivalSet v ell := by
    filter_upwards [costKernel_exponent_nonincreasing v z] with y hy
    exact not_lt_of_ge (le_trans hy hZ)
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using h

theorem harmonicKernel_no_reentry (v ell : ℝ) (z : CostState) (hz : z ∉ arrivalSet v ell) :
    harmonicKernel z (arrivalSet v ell) = 0 :=
  harmonicKernel_absolutelyContinuous z (costKernel_no_reentry v ell z hz)

end NumberTheoryLean.ArrivalKernelGeometry

end

end Erdos970

end OAI
