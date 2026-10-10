import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Partitions.CompletedParentInterval
import OAI.NumberTheory.Jacobsthal.Partitions.CrossingBandGeometry
import OAI.NumberTheory.Jacobsthal.Partitions.MeshBoundaryGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Finset
open scoped BigOperators
namespace Erdos970Dependency.MaximalCoupling

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

noncomputable def common (a b : ι → ℝ) (i : ι) : ℝ := min (a i) (b i)
noncomputable def residual (a b : ι → ℝ) : ℝ := 1 - ∑ i, common a b i
noncomputable def leftRemainder (a b : ι → ℝ) (i : ι) : ℝ := a i - common a b i
noncomputable def rightRemainder (a b : ι → ℝ) (i : ι) : ℝ := b i - common a b i

noncomputable def matrix (a b : ι → ℝ) (i j : ι) : ℝ :=
  (if i = j then common a b i else 0) +
    if residual a b = 0 then 0 else leftRemainder a b i * rightRemainder a b j / residual a b

omit [Fintype ι] in
theorem common_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) :
    0 ≤ common a b i := le_min (ha i) (hb i)

omit [Fintype ι] in
theorem leftRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ leftRemainder a b i :=
  sub_nonneg.mpr (min_le_left _ _)
omit [Fintype ι] in
theorem rightRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ rightRemainder a b i :=
  sub_nonneg.mpr (min_le_right _ _)

theorem sum_leftRemainder {a b : ι → ℝ} (ha : ∑ i, a i = 1) :
    ∑ i, leftRemainder a b i = residual a b := by simp only [leftRemainder, sum_sub_distrib, ha, residual]
theorem sum_rightRemainder {a b : ι → ℝ} (hb : ∑ i, b i = 1) :
    ∑ i, rightRemainder a b i = residual a b := by simp only [rightRemainder, sum_sub_distrib, hb, residual]

theorem residual_nonneg {a b : ι → ℝ} (ha : ∑ i, a i = 1) : 0 ≤ residual a b := by
  rw [← sum_leftRemainder ha]
  exact sum_nonneg (fun i _ => leftRemainder_nonneg a b i)

theorem leftRemainder_zero {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hr : residual a b = 0) (i : ι) :
    leftRemainder a b i = 0 := by
  have h := single_le_sum (fun j _ => leftRemainder_nonneg a b j) (mem_univ i)
  rw [sum_leftRemainder ha, hr] at h
  exact le_antisymm h (leftRemainder_nonneg a b i)
theorem rightRemainder_zero {a b : ι → ℝ} (hb : ∑ i, b i = 1) (hr : residual a b = 0) (i : ι) :
    rightRemainder a b i = 0 := by
  have h := single_le_sum (fun j _ => rightRemainder_nonneg a b j) (mem_univ i)
  rw [sum_rightRemainder hb, hr] at h
  exact le_antisymm h (rightRemainder_nonneg a b i)

omit [Fintype ι] in

theorem remainder_product_self (a b : ι → ℝ) (i : ι) :
    leftRemainder a b i * rightRemainder a b i = 0 := by
  rcases le_total (a i) (b i) with h | h
  · simp [leftRemainder, rightRemainder, common, min_eq_left h]
  · simp [leftRemainder, rightRemainder, common, min_eq_right h]

theorem matrix_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i = 1) (i j : ι) : 0 ≤ matrix a b i j := by
  unfold matrix
  apply add_nonneg
  · split_ifs <;> first | exact common_nonneg ha hb i | exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (leftRemainder_nonneg a b i) (rightRemainder_nonneg a b j)) (residual_nonneg hsa)

theorem row_sum {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) (i : ι) :
    ∑ j, matrix a b i j = a i := by
  classical
  by_cases hr : residual a b = 0
  · have hz := leftRemainder_zero ha hr i
    simp only [matrix, ite_eq_left hr, add_zero]
    simp only [sum_ite_eq, mem_univ, ite_true]
    unfold leftRemainder at hz
    linarith
  · simp only [matrix, ite_eq_right hr, sum_add_distrib]
    rw [sum_ite_eq]
    simp only [mem_univ, ite_true]
    rw [← sum_div, ← mul_sum, sum_rightRemainder hb]
    rw [mul_div_cancel_right₀ _ hr]
    unfold leftRemainder
    ring

theorem column_sum {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) (j : ι) :
    ∑ i, matrix a b i j = b j := by
  classical
  by_cases hr : residual a b = 0
  · have hz := rightRemainder_zero hb hr j
    simp only [matrix, ite_eq_left hr, add_zero]
    simp only [sum_ite_eq', mem_univ, ite_true]
    unfold rightRemainder at hz
    linarith
  · simp only [matrix, ite_eq_right hr, sum_add_distrib]
    rw [sum_ite_eq']
    simp only [mem_univ, ite_true]
    rw [← sum_div, ← sum_mul, sum_leftRemainder ha]
    rw [mul_div_cancel_left₀ _ hr]
    unfold rightRemainder
    ring

theorem matrix_diagonal (a b : ι → ℝ) (i : ι) : matrix a b i i = common a b i := by
  simp [matrix, remainder_product_self]

theorem total_mass {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) :
    ∑ i, ∑ j, matrix a b i j = 1 := by simp_rw [row_sum ha hb]; exact ha

theorem mismatch_mass {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) :
    (∑ i, ∑ j, if i ≠ j then matrix a b i j else 0) = residual a b := by
  classical
  have hi (i : ι) : (∑ j, if i ≠ j then matrix a b i j else 0) + matrix a b i i = a i := by
    have h := sum_filter_add_sum_filter_not (univ : Finset ι) (fun j => i ≠ j) (fun j => matrix a b i j)
    simp only [sum_filter, not_not, sum_ite_eq, mem_univ, ite_true, row_sum ha hb] at h
    exact h
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hi)
  simp only [sum_add_distrib, matrix_diagonal, ha] at hsum
  unfold residual
  linarith

theorem exists_coupling {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i = 1) (hsb : ∑ i, b i = 1) :
    ∃ p : ι → ι → ℝ, (∀ i j, 0 ≤ p i j) ∧ (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j) ∧
      (∑ i, ∑ j, if i ≠ j then p i j else 0) = 1 - ∑ i, min (a i) (b i) := by
  exact ⟨matrix a b, matrix_nonneg ha hb hsa, row_sum hsa hsb, column_sum hsa hsb,
    mismatch_mass hsa hsb⟩

end Erdos970Dependency.MaximalCoupling

end

section

namespace NumberTheoryLean.KernelBinConditioning

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def conditional (K : Kernel α β) {B : Set β} (hB : MeasurableSet B) (default : β) : Kernel α β where
  toFun x := if K x B = 0 then Measure.dirac default else (K x B)⁻¹ • (K x).restrict B
  measurable' := by
    classical
    have hm := K.measurable_coe hB
    have hscaled : Measurable (fun x => (K x B)⁻¹ • (K x).restrict B) := by
      apply Measure.measurable_of_measurable_coe
      intro A hA
      simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
      exact hm.inv.mul (K.measurable_coe (hA.inter hB))
    exact Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const hscaled

theorem conditional_apply (K : Kernel α β) {B : Set β} (hB : MeasurableSet B) (default : β) (x : α) :
    conditional K hB default x = if K x B = 0 then Measure.dirac default else (K x B)⁻¹ • (K x).restrict B := rfl

instance conditional_isMarkov (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) : IsMarkovKernel (conditional K hB default) := by
  constructor
  intro x
  constructor
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx]
    exact measure_univ
  · rw [ite_eq_right hx, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hx (measure_ne_top _ _)

theorem weighted_conditional (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) (x : α) :
    (K x B) • conditional K hB default x = (K x).restrict B := by
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx, hx, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hx).symm
  · rw [ite_eq_right hx, smul_smul, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_smul]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def labelMass (K : Kernel α β) (label : β → ι) (x : α) (i : ι) : ℝ :=
  (K x (label ⁻¹' {i})).toReal

theorem labelMass_measurable (K : Kernel α β) {label : β → ι} (hl : Measurable label) (i : ι) :
    Measurable (fun x => labelMass K label x i) :=
  ENNReal.measurable_toReal.comp (K.measurable_coe (hl (measurableSet_singleton i)))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem labelMass_nonneg (K : Kernel α β) (label : β → ι) (x : α) (i : ι) :
    0 ≤ labelMass K label x i := ENNReal.toReal_nonneg

theorem conditional_map_label (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (default : β) (x : α) (i : ι) (hi : K x (label ⁻¹' {i}) ≠ 0) :
    (conditional K (hl (measurableSet_singleton i)) default x).map label = Measure.dirac i := by
  have hAE : ∀ᵐ y ∂conditional K (hl (measurableSet_singleton i)) default x, label y = i := by
    rw [conditional_apply, ite_eq_right hi]
    apply Measure.ae_smul_measure
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      ae_restrict_mem (hl (measurableSet_singleton i)) (μ := K x)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hl, lintegral_dirac' _ hf]
  calc
    _ = ∫⁻ _y, f i ∂conditional K (hl (measurableSet_singleton i)) default x :=
      lintegral_congr_ae (hAE.mono (fun y hy => congrArg f hy))
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

variable [Fintype ι]

theorem labelMass_sum (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (x : α) : ∑ i, labelMass K label x i = 1 := by
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ENNReal.toReal_one] at hr
  exact hr

theorem conditional_mixture (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (default : β) (x : α) :
    (∑ i, (K x (label ⁻¹' {i})) • conditional K (hl (measurableSet_singleton i)) default x) = K x := by
  simp_rw [weighted_conditional]
  apply Measure.ext
  intro B hB
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.restrict_apply hB]
  have h := sum_measure_preimage_singleton (μ := (K x).restrict B) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
  have heq : ∀ i : ι, (K x).restrict B (label ⁻¹' {i}) = K x (B ∩ label ⁻¹' {i}) := by
    intro i
    rw [Measure.restrict_apply (hl (measurableSet_singleton i)), Set.inter_comm]
  simp_rw [heq] at h
  exact h

end NumberTheoryLean.KernelBinConditioning

end

section

namespace NumberTheoryLean.KernelCouplingWeights

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning Erdos970Dependency.MaximalCoupling
attribute [local instance] Classical.propDecidable

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def weight (K : Kernel α β) (L : Kernel α γ) (f : β → ι) (g : γ → ι)
    (x : α) (i j : ι) : ℝ := matrix (labelMass K f x) (labelMass L g x) i j

noncomputable def errorMass (K : Kernel α β) (L : Kernel α γ) (f : β → ι) (g : γ → ι) (x : α) : ℝ :=
  residual (labelMass K f x) (labelMass L g x)

theorem weight_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) : Measurable (fun x => weight K L f g x i j) := by
  classical
  have ha := labelMass_measurable K hf
  have hb := labelMass_measurable L hg
  have hc (i : ι) : Measurable (fun x => common (labelMass K f x) (labelMass L g x) i) := (ha i).min (hb i)
  have hr : Measurable (fun x => residual (labelMass K f x) (labelMass L g x)) :=
    measurable_const.sub (Finset.measurable_sum univ (fun i _ => hc i))
  have hl : Measurable (fun x => leftRemainder (labelMass K f x) (labelMass L g x) i) := (ha i).sub (hc i)
  have hh : Measurable (fun x => rightRemainder (labelMass K f x) (labelMass L g x) j) := (hb j).sub (hc j)
  have hd : Measurable (fun x => if i = j then common (labelMass K f x) (labelMass L g x) i else 0) := by
    by_cases hij : i = j
    · simpa only [ite_eq_left hij] using hc i
    · simp only [ite_eq_right hij]
      exact measurable_const
  exact hd.add (Measurable.ite (measurableSet_eq_fun hr measurable_const) measurable_const ((hl.mul hh).div hr))

theorem weight_joint_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) :
    Measurable (Function.uncurry (fun (x : α) (_ : β × γ) => ENNReal.ofReal (weight K L f g x i j))) :=
  (ENNReal.measurable_ofReal.comp (weight_measurable K L hf hg i j)).comp measurable_fst

variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g)
include hf hg

omit hg [IsMarkovKernel L] in
theorem weight_nonnegative (x : α) (i j : ι) : 0 ≤ weight K L f g x i j :=
  matrix_nonneg (labelMass_nonneg K f x) (labelMass_nonneg L g x) (labelMass_sum K hf x) i j

theorem weight_row (x : α) (i : ι) : ∑ j, weight K L f g x i j = labelMass K f x i :=
  row_sum (labelMass_sum K hf x) (labelMass_sum L hg x) i

theorem weight_column (x : α) (j : ι) : ∑ i, weight K L f g x i j = labelMass L g x j :=
  column_sum (labelMass_sum K hf x) (labelMass_sum L hg x) j

theorem weight_total (x : α) : ∑ i, ∑ j, weight K L f g x i j = 1 :=
  total_mass (labelMass_sum K hf x) (labelMass_sum L hg x)

theorem weight_row_ofReal (x : α) (i : ι) :
    ∑ j, ENNReal.ofReal (weight K L f g x i j) = K x (f ⁻¹' {i}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => weight_nonnegative K L (g := g) hf x i j), weight_row K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_column_ofReal (x : α) (j : ι) :
    ∑ i, ENNReal.ofReal (weight K L f g x i j) = L x (g ⁻¹' {j}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => weight_nonnegative K L (g := g) hf x i j), weight_column K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_total_ofReal (x : α) : ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) = 1 := by
  simp_rw [weight_row_ofReal K L hf hg]
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hf (measurableSet_singleton i))
  simpa only [Finset.coe_univ, Set.preimage_univ, measure_univ] using h

theorem weight_le_left (x : α) (i j : ι) : weight K L f g x i j ≤ labelMass K f x i := by
  have h := single_le_sum (fun j _ => weight_nonnegative K L (g := g) hf x i j) (Finset.mem_univ j)
  rwa [weight_row K L hf hg] at h

theorem weight_le_right (x : α) (i j : ι) : weight K L f g x i j ≤ labelMass L g x j := by
  have h := single_le_sum (fun i _ => weight_nonnegative K L (g := g) hf x i j) (Finset.mem_univ i)
  rwa [weight_column K L hf hg] at h

theorem weight_zero_left (x : α) (i j : ι) (hi : K x (f ⁻¹' {i}) = 0) : weight K L f g x i j = 0 := by
  apply le_antisymm _ (weight_nonnegative K L (g := g) hf x i j)
  have h := weight_le_left K L hf hg x i j
  simpa only [labelMass, hi, ENNReal.toReal_zero] using h

theorem weight_zero_right (x : α) (i j : ι) (hj : L x (g ⁻¹' {j}) = 0) : weight K L f g x i j = 0 := by
  apply le_antisymm _ (weight_nonnegative K L (g := g) hf x i j)
  have h := weight_le_right K L hf hg x i j
  simpa only [labelMass, hj, ENNReal.toReal_zero] using h

theorem weight_mismatch (x : α) :
    (∑ i, ∑ j, if i ≠ j then weight K L f g x i j else 0) = errorMass K L f g x := by
  exact mismatch_mass (labelMass_sum K hf x) (labelMass_sum L hg x)

end NumberTheoryLean.KernelCouplingWeights

end

section

namespace NumberTheoryLean.KernelCouplingLift

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning KernelCouplingWeights

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g) (dβ : β) (dγ : γ)

noncomputable def component (i j : ι) : Kernel α (β × γ) :=
  ((conditional K (hf (measurableSet_singleton i)) dβ).prod
    (conditional L (hg (measurableSet_singleton j)) dγ)).withDensity
      (fun x _ => ENNReal.ofReal (weight K L f g x i j))

instance component_isSFinite (i j : ι) : IsSFiniteKernel (component K L hf hg dβ dγ i j) := by
  unfold component
  apply Kernel.IsSFiniteKernel.withDensity
  intro x y
  exact ENNReal.ofReal_ne_top

theorem component_apply (i j : ι) (x : α) :
    component K L hf hg dβ dγ i j x = ENNReal.ofReal (weight K L f g x i j) •
      (conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x) := by
  rw [component, Kernel.withDensity_apply _ (weight_joint_measurable K L hf hg i j) x,
    Kernel.prod_apply, withDensity_const]

noncomputable def coupled : Kernel α (β × γ) :=
  Kernel.sum (fun p : ι × ι => component K L hf hg dβ dγ p.1 p.2)

instance coupled_isSFinite : IsSFiniteKernel (coupled K L hf hg dβ dγ) := by
  unfold coupled
  infer_instance

theorem coupled_apply_set (x : α) {B : Set (β × γ)} (hB : MeasurableSet B) :
    coupled K L hf hg dβ dγ x B = ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) *
      ((conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x)) B := by
  rw [coupled, Kernel.sum_apply' _ _ hB, tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [component_apply, Measure.smul_apply, smul_eq_mul]

instance coupled_isMarkov : IsMarkovKernel (coupled K L hf hg dβ dγ) := by
  constructor
  intro x
  constructor
  rw [coupled_apply_set K L hf hg dβ dγ x MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  exact weight_total_ofReal K L hf hg x

theorem coupled_map_fst (x : α) :
    (coupled K L hf hg dβ dγ x).map Prod.fst = K x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_fst hB, coupled_apply_set K L hf hg dβ dγ x (measurable_fst hB)]
  have hpre : (Prod.fst ⁻¹' B : Set (β × γ)) = B ×ˢ univ := by ext p; simp
  rw [hpre]
  simp only [Measure.prod_prod, measure_univ, mul_one]
  simp_rw [← Finset.sum_mul, weight_row_ofReal K L hf hg]
  have h := congrArg (fun μ : Measure β => μ B) (conditional_mixture K hf dβ x)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

theorem coupled_map_snd (x : α) :
    (coupled K L hf hg dβ dγ x).map Prod.snd = L x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_snd hB, coupled_apply_set K L hf hg dβ dγ x (measurable_snd hB)]
  have hpre : (Prod.snd ⁻¹' B : Set (β × γ)) = univ ×ˢ B := by ext p; simp
  rw [hpre]
  simp only [Measure.prod_prod, measure_univ, one_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, weight_column_ofReal K L hf hg]
  have h := congrArg (fun μ : Measure γ => μ B) (conditional_mixture L hg dγ x)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

end NumberTheoryLean.KernelCouplingLift

end

section

namespace NumberTheoryLean.KernelCouplingLabels

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning KernelCouplingWeights KernelCouplingLift
open Erdos970Dependency.MaximalCoupling

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g) (dβ : β) (dγ : γ)
include hf hg

theorem component_labels (i j : ι) (x : α) :
    (component K L hf hg dβ dγ i j x).map (Prod.map f g) =
      ENNReal.ofReal (weight K L f g x i j) • Measure.dirac (i,j) := by
  by_cases hi : K x (f ⁻¹' {i}) = 0
  · simp only [component_apply, weight_zero_left K L hf hg x i j hi, ENNReal.ofReal_zero, zero_smul, Measure.map_zero]
  · by_cases hj : L x (g ⁻¹' {j}) = 0
    · simp only [component_apply, weight_zero_right K L hf hg x i j hj, ENNReal.ofReal_zero, zero_smul, Measure.map_zero]
    · rw [component_apply, Measure.map_smul _ (hf.prodMap hg).aemeasurable, ← Measure.map_prod_map _ _ hf hg,
        conditional_map_label K hf dβ x i hi, conditional_map_label L hg dγ x j hj,
        Measure.dirac_prod_dirac]

theorem coupled_labels (x : α) :
    (coupled K L hf hg dβ dγ x).map (Prod.map f g) =
      Measure.sum (fun p : ι × ι => ENNReal.ofReal (weight K L f g x p.1 p.2) • Measure.dirac p) := by
  rw [coupled, Kernel.sum_apply, Measure.map_sum (hf.prodMap hg).aemeasurable]
  apply congrArg Measure.sum
  funext p
  exact component_labels K L hf hg dβ dγ p.1 p.2 x

theorem coupled_mismatch (x : α) :
    coupled K L hf hg dβ dγ x {p : β × γ | f p.1 ≠ g p.2} =
      ENNReal.ofReal (errorMass K L f g x) := by
  classical
  let D : Set (ι × ι) := {p | p.1 ≠ p.2}
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  change coupled K L hf hg dβ dγ x ((Prod.map f g) ⁻¹' D) = _
  rw [← Measure.map_apply (hf.prodMap hg) hD, coupled_labels, Measure.sum_apply _ hD,
    tsum_fintype, Fintype.sum_prod_type]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hD, Set.indicator,
    D, Set.mem_ofPred_eq, Pi.one_apply, mul_ite, mul_one, mul_zero]
  have hn (i j : ι) : 0 ≤ if i ≠ j then weight K L f g x i j else 0 := by
    split_ifs
    · exact weight_nonnegative K L (g := g) hf x i j
    · exact le_rfl
  have he : (∑ i, ∑ j, if i ≠ j then ENNReal.ofReal (weight K L f g x i j) else 0) =
      ENNReal.ofReal (∑ i, ∑ j, if i ≠ j then weight K L f g x i j else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hn i j)]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  rw [he, weight_mismatch K L hf hg]

omit hg [IsMarkovKernel L] in
theorem errorMass_le_l1 (x : α) : errorMass K L f g x ≤
    ∑ i, |labelMass K f x i-labelMass L g x i| := by
  rw [errorMass, ← sum_leftRemainder (labelMass_sum K hf x)]
  apply Finset.sum_le_sum
  intro i hi
  unfold leftRemainder common
  rcases le_total (labelMass K f x i) (labelMass L g x i) with hab | hba
  · rw [min_eq_left hab, sub_self]
    exact abs_nonneg _
  · rw [min_eq_right hba]
    exact le_abs_self _

theorem coupled_mismatch_le_l1 (x : α) :
    coupled K L hf hg dβ dγ x {p : β × γ | f p.1 ≠ g p.2} ≤
      ENNReal.ofReal (∑ i, |labelMass K f x i-labelMass L g x i|) := by
  rw [coupled_mismatch]
  exact ENNReal.ofReal_le_ofReal (errorMass_le_l1 K L (g := g) hf x)

end NumberTheoryLean.KernelCouplingLabels

end

section

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelCouplingLabels KernelBinConditioning

abbrev JointState (w ell S : ℝ) (start : Node) :=
  ChainState w ell S start × CemeteryKernel.Space CostState

noncomputable def primeLabel (w ell S mesh : ℝ) (start : Node) : ChainState w ell S start → Label S mesh
  | none => cemeteryLabel S mesh
  | some h => ratioLabel S mesh h.node.ratio

noncomputable def continuousLabel (S mesh : ℝ) : CemeteryKernel.Space CostState → Label S mesh :=
  Sum.elim (fun z => ratioLabel S mesh (stateRatio z.1)) (fun _ => cemeteryLabel S mesh)

theorem primeLabel_measurable (w ell S mesh : ℝ) (start : Node) : Measurable (primeLabel w ell S mesh start) :=
  measurable_of_countable _

theorem continuousLabel_measurable (S mesh : ℝ) : Measurable (continuousLabel S mesh) :=
  ((ratioLabel_measurable S mesh).comp (stateRatio_measurable.comp measurable_fst)).sumElim measurable_const

noncomputable def primeParent (w ell S : ℝ) (start : Node) : Kernel (JointState w ell S start) (ChainState w ell S start) :=
  (chain w ell S start).comap Prod.fst measurable_fst

noncomputable def continuousParent (w ell S : ℝ) (start : Node) (v : ℝ) :
    Kernel (JointState w ell S start) (CemeteryKernel.Space CostState) :=
  (continuousChain v ell S).comap Prod.snd measurable_snd

instance primeParent_isMarkov (w ell S : ℝ) (start : Node) [IsMarkovKernel (chain w ell S start)] :
    IsMarkovKernel (primeParent w ell S start) := by unfold primeParent; infer_instance

instance continuousParent_isMarkov (w ell S : ℝ) (start : Node) (v : ℝ) :
    IsMarkovKernel (continuousParent w ell S start v) := by unfold continuousParent; infer_instance

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def jointKernel
    (_hw : normalizationThreshold ≤ w) (_hell : 1 ≤ ell) (_hS0 : 0 ≤ S) (_hS : S ≤ (Real.log w)^3)
    (_hr : 0 < start.gap) (_hs : Valid start.side start.ratio) (_hsS : start.ratio ≤ S)
    (v mesh : ℝ) : Kernel (JointState w ell S start) (JointState w ell S start) := by
  letI := chain_isMarkov _hw _hell _hS0 _hS _hr _hs _hsS
  exact coupled (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead

instance jointKernel_isMarkov (v mesh : ℝ) : IsMarkovKernel (jointKernel hw hell hS0 hS hr hs hsS v mesh) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold jointKernel
  infer_instance

theorem jointKernel_left (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    (jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.fst = chain w ell S start p := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_map_fst (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

theorem jointKernel_right (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    (jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.snd = continuousChain v ell S z := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_map_snd (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

theorem jointKernel_mismatch_bound (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)
      {q | primeLabel w ell S mesh start q.1 ≠ continuousLabel S mesh q.2} ≤
      ENNReal.ofReal (∑ i : Label S mesh,
        |(chain w ell S start p ((primeLabel w ell S mesh start) ⁻¹' {i})).toReal -
          (continuousChain v ell S z ((continuousLabel S mesh) ⁻¹' {i})).toReal|) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_mismatch_le_l1 (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

end NumberTheoryLean.ActualProcessCoupling

end

section

namespace NumberTheoryLean.ActualCouplingSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels ActualProcessCoupling LowStateHorizon

variable {w ell S : ℝ} {start : Node}

def continuousSupported (S : ℝ) : CemeteryKernel.Space CostState → Prop
  | .inl z => stateRatio z.1 ≤ S
  | .inr _ => True

def badRatio (S : ℝ) : Set CostState := {z | ¬stateRatio z.1 ≤ S}

theorem badRatio_measurable (S : ℝ) : MeasurableSet (badRatio S) :=
  (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).compl

theorem unsupported_eq (S : ℝ) :
    {q : CemeteryKernel.Space CostState | ¬continuousSupported S q} = Sum.inl '' badRatio S := by
  ext q
  cases q <;> simp [continuousSupported,badRatio]

theorem continuousSupported_measurable (S : ℝ) : MeasurableSet {q | continuousSupported S q} := by
  have h : MeasurableSet {q : CemeteryKernel.Space CostState | ¬continuousSupported S q} := by
    rw [unsupported_eq]
    exact (badRatio_measurable S).inl_image
  simpa only [Set.compl_ofPred, not_not] using h.compl

theorem continuous_supported (v ell S : ℝ) (q : CemeteryKernel.Space CostState) :
    ∀ᵐ y ∂continuousChain v ell S q, continuousSupported S y := by
  apply ae_iff.mpr
  rw [unsupported_eq]
  cases q with
  | inl z =>
    rw [continuousChain, CemeteryKernel.complete_live_mass _ _ (badRatio_measurable S),
      lowKernel, Kernel.restrict_apply, Measure.restrict_apply (badRatio_measurable S)]
    have he : badRatio S ∩ lowDomain v ell S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.1 hy.2.2
    rw [he,measure_empty]
  | inr u =>
    cases u
    change Measure.dirac (CemeteryKernel.dead : CemeteryKernel.Space CostState) (Sum.inl '' badRatio S) = 0
    rw [Measure.dirac_apply' _ (badRatio_measurable S).inl_image, indicator_of_notMem (by simp [CemeteryKernel.dead])]

def matchedOutcome (mesh : ℝ) : JointState w ell S start → Prop
  | (none,.inr _) => True
  | (some h,.inl z) => |h.node.ratio-stateRatio z.1| < mesh
  | _ => False

theorem labels_match_outcomes {mesh : ℝ} (hm : 0 < mesh)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState)
    (hSup : continuousSupported S z) (hlabel : primeLabel w ell S mesh start p = continuousLabel S mesh z) :
    matchedOutcome mesh (p,z) := by
  cases p with
  | none =>
    cases z with
    | inl z =>
      change cemeteryLabel S mesh = ratioLabel S mesh (stateRatio z.1) at hlabel
      exact False.elim (ratioLabel_ne_cemetery hm hSup hlabel.symm)
    | inr u => trivial
  | some h =>
    have hpos := valid_pos (terminal_valid hs h.admissible)
    have hbound := terminal_ratio_le hsS h.admissible
    cases z with
    | inl z =>
      change ratioLabel S mesh h.node.ratio = ratioLabel S mesh (stateRatio z.1) at hlabel
      exact matching_ratios_close hm hpos.le (OccupationBoundaries.stateRatio_pos z.1).le hbound hSup hlabel
    | inr u =>
      change ratioLabel S mesh h.node.ratio = cemeteryLabel S mesh at hlabel
      exact False.elim (ratioLabel_ne_cemetery hm hbound hlabel)

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_continuous_supported (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z), continuousSupported S q.2 := by
  have h : ∀ᵐ q ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.snd, continuousSupported S q := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    exact continuous_supported v ell S z
  exact (ae_map_iff measurable_snd.aemeasurable (continuousSupported_measurable S)).mp h

theorem joint_matching_control (v : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z),
      primeLabel w ell S mesh start q.1 = continuousLabel S mesh q.2 → matchedOutcome mesh q := by
  filter_upwards [joint_continuous_supported hw hell hS0 hS hr hs hsS v mesh p z] with q hq
  intro heq
  exact labels_match_outcomes hm hs hsS q.1 q.2 hq heq

end NumberTheoryLean.ActualCouplingSupport

end

section

namespace NumberTheoryLean.ActualCouplingFinite

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ContinuousKilledBins PrimeChainHorizon LowStateHorizon

section Generic
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (K : Kernel α α) (L : Kernel β β)
variable {f : α → β} (hf : Measurable f)

include hf

theorem map_power_of_step (hstep : ∀ x, (K x).map f = L (f x)) (n : ℕ) (x : α) :
    ((K^n) x).map f = (L^n) (f x) := by
  let P : Kernel α β := Kernel.deterministic f hf
  have hinter : P ∘ₖ K = L ∘ₖ P := by
    rw [show P = Kernel.deterministic f hf from rfl, Kernel.deterministic_comp_eq_map,
      Kernel.comp_deterministic_eq_comap]
    ext x : 1
    rw [Kernel.map_apply _ hf,Kernel.comap_apply]
    exact hstep x
  have hpow : ∀ n, P ∘ₖ (K^n) = (L^n) ∘ₖ P := by
    intro n
    induction n with
    | zero =>
      change P ∘ₖ (Kernel.id : Kernel α α) = Kernel.id ∘ₖ P
      rw [Kernel.comp_id,Kernel.id_comp]
    | succ n ih =>
      have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
      have hq : L^(n+1) = (L^n) ∘ₖ L := pow_succ _ _
      rw [hp,hq,← Kernel.comp_assoc,ih,Kernel.comp_assoc,hinter,← Kernel.comp_assoc]
  have h := hpow n
  rw [show P = Kernel.deterministic f hf from rfl,Kernel.deterministic_comp_eq_map,
    Kernel.comp_deterministic_eq_comap] at h
  have hx := congrArg (fun M : Kernel α β => M x) h
  rwa [Kernel.map_apply _ hf,Kernel.comap_apply] at hx
end Generic

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance jointKernel_pow_markov (v mesh : ℝ) (n : ℕ) :
    IsMarkovKernel ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (JointState w ell S start) (JointState w ell S start)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (jointKernel hw hell hS0 hS hr hs hsS v mesh)^(n+1) =
      (jointKernel hw hell hS0 hS hr hs hsS v mesh) ∘ₖ ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := pow_succ' _ _
    rw [hp]
    infer_instance

theorem joint_power_left (v mesh : ℝ) (n : ℕ) (q : JointState w ell S start) :
    (((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) q).map Prod.fst =
      ((chain w ell S start)^n) q.1 := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact map_power_of_step _ _ measurable_fst
    (fun x => jointKernel_left hw hell hS0 hS hr hs hsS v mesh x.1 x.2) n q

theorem joint_power_right (v mesh : ℝ) (n : ℕ) (q : JointState w ell S start) :
    (((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) q).map Prod.snd =
      ((continuousChain v ell S)^n) q.2 :=
  map_power_of_step _ _ measurable_snd
    (fun x => jointKernel_right hw hell hS0 hS hr hs hsS v mesh x.1 x.2) n q

noncomputable def jointPathLaw (v mesh : ℝ) (z : CostState) (n : ℕ) : Measure (JointState w ell S start) :=
  ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) (some History.empty,.inl z)

instance jointPathLaw_probability (v mesh : ℝ) (z : CostState) (n : ℕ) :
    IsProbabilityMeasure (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n) := by
  unfold jointPathLaw
  infer_instance

theorem jointPathLaw_prime (v mesh : ℝ) (z : CostState) (n : ℕ) :
    (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.fst = pathLaw w ell S start n :=
  joint_power_left hw hell hS0 hS hr hs hsS v mesh n (some History.empty,.inl z)

theorem jointPathLaw_continuous (v mesh : ℝ) (z : CostState) (n : ℕ) :
    (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.snd =
      ((continuousChain v ell S)^n) (.inl z) :=
  joint_power_right hw hell hS0 hS hr hs hsS v mesh n (some History.empty,.inl z)

theorem jointPathLaw_stage (v mesh : ℝ) (z : CostState) (n : ℕ) :
    ∀ᵐ q ∂jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n, stage n q.1 := by
  have h : ∀ᵐ p ∂(jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.fst, stage n p := by
    rw [jointPathLaw_prime hw hell hS0 hS hr hs hsS]
    exact pathLaw_stage n
  exact (ae_map_iff measurable_fst.aemeasurable (stage_measurable n)).mp h

theorem jointPathLaw_prime_exit {B : ℝ} (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B)
    (v mesh : ℝ) (z : CostState) (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    ∀ᵐ q ∂jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n, q.1 = none := by
  have h : ∀ᵐ p ∂(jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.fst, p = none := by
    rw [jointPathLaw_prime hw hell hS0 hS hr hs hsS,
      pathLaw_eq_cemetery hw hell hS0 hS hr hs hsS hB hsize n hn]
    exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
  exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_singleton _)).mp h

end NumberTheoryLean.ActualCouplingFinite

end

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ContinuousKilledBins
open LowStateHorizon NearbyParentGeometry ArrivalKernelGeometry RegeneratingInverseBands
open PrimeTiltGeometry PrimeHistoryHorizon KernelDensityBridge PairedCostGrouping

variable {w ell S : ℝ} {start : Node}

def liftPredicate {α : Type*} (P : α → Prop) : CemeteryKernel.Space α → Prop :=
  Sum.elim P (fun _ => True)

theorem liftPredicate_measurable {α : Type*} [MeasurableSpace α] {P : α → Prop}
    (hP : MeasurableSet {x | P x}) : MeasurableSet {x | liftPredicate P x} := by
  exact measurableSet_sum_iff.mpr ⟨hP,MeasurableSet.univ⟩

theorem complete_ae {α : Type*} [MeasurableSpace α] (K : Kernel α α) (x : α)
    {P : α → Prop} (hP : MeasurableSet {y | P y}) (h : ∀ᵐ y ∂K x, P y) :
    ∀ᵐ y ∂CemeteryKernel.complete K (.inl x), liftPredicate P y := by
  rw [CemeteryKernel.complete_live,CemeteryKernel.liveRow_apply,ae_add_measure_iff]
  constructor
  · exact (ae_map_iff measurable_inl.aemeasurable (liftPredicate_measurable hP)).mpr h
  · apply Measure.ae_smul_measure _ _
    exact (ae_dirac_iff (liftPredicate_measurable hP)).mpr trivial

def primeFollows (h : History w ell S start) : ChainState w ell S start → Prop
  | none => True
  | some k => ∃ p, ∃ hp : p ∈ nodeChildren w ell S h.node, k = h.append p hp

theorem prime_follows (h : History w ell S start) :
    ∀ᵐ k ∂chain w ell S start (some h), primeFollows h k := by
  classical
  apply ae_iff.mpr
  simp [chain_some,completedLaw,liveLaw,primeFollows]
  intro p hp
  exact Or.inr ⟨p,hp,rfl⟩

theorem side_set_measurable (i : Side) : MeasurableSet {s : State | stateSide s = i} := by
  cases i <;> apply measurableSet_sum_iff.mpr <;> simp [stateSide]

theorem stateKernel_side (s : State) :
    ∀ᵐ t ∂stateKernel s, stateSide t = (stateSide s).flip := by
  cases s with
  | inl s =>
    change ∀ᵐ t ∂evenBranch s, stateSide t = Side.odd
    rw [evenBranch,Kernel.map_apply _ measurable_inr]
    exact (ae_map_iff measurable_inr.aemeasurable (side_set_measurable .odd)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))
  | inr s =>
    change ∀ᵐ t ∂oddBranch s, stateSide t = Side.even
    rw [oddBranch,Kernel.map_apply _ measurable_inl]
    exact (ae_map_iff measurable_inl.aemeasurable (side_set_measurable .even)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))

def continuousFollows (z y : CostState) : Prop :=
  y.2 = z.2+cost (stateRatio y.1) ∧ stateSide y.1 = (stateSide z.1).flip

theorem continuousFollows_measurable (z : CostState) : MeasurableSet {y | continuousFollows z y} :=
  (measurableSet_eq_fun measurable_snd
    (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst)))).inter
    (measurable_fst (side_set_measurable (stateSide z.1).flip))

theorem costKernel_follows (z : CostState) : ∀ᵐ y ∂costKernel z, continuousFollows z y := by
  have hm : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable (continuousFollows_measurable z)).mpr
  filter_upwards [stateKernel_side z.1] with y hy
  exact ⟨rfl,hy⟩

theorem continuous_follows (v ell S : ℝ) (z : CostState) :
    ∀ᵐ y ∂continuousChain v ell S (.inl z), liftPredicate (continuousFollows z) y := by
  apply complete_ae _ _ (continuousFollows_measurable z)
  exact ae_restrict_of_ae (costKernel_follows z)

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_follows (v mesh : ℝ) (h : History w ell S start) (z : CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z),
      primeFollows h q.1 ∧ liftPredicate (continuousFollows z) q.2 := by
  have hL : ∀ᵐ p ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z)).map Prod.fst,
      primeFollows h p := by
    rw [jointKernel_left hw hell hS0 hS hr hs hsS]
    exact prime_follows h
  have hR : ∀ᵐ y ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z)).map Prod.snd,
      liftPredicate (continuousFollows z) y := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    exact continuous_follows v ell S z
  exact ((ae_map_iff measurable_fst.aemeasurable (show MeasurableSet {p | primeFollows h p} from trivial)).mp hL).and
    ((ae_map_iff measurable_snd.aemeasurable (liftPredicate_measurable (continuousFollows_measurable z))).mp hR)

include hell hr hs

theorem prime_step_gap (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node.gap = nextGap h.node.gap (h.append p hp).node.ratio := by
  have hrg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hvalid := terminal_valid hs h.admissible
  rw [History.append_node]
  exact (nextGap_childRatio hrg (child_exponent_positive (show 0 ≤ ell by linarith) hp)
    (valid_pos (child_valid hvalid hp))).symm

theorem matched_live_update {v mesh d : ℝ} (h k : History w ell S start) (z y : CostState)
    (hfollow : primeFollows h (some k)) (hcont : continuousFollows z y)
    (hside : h.node.side = stateSide z.1)
    (hgap : |Real.log h.node.gap-Real.log (gapValue v z)| ≤ d)
    (hmatch : |k.node.ratio-stateRatio y.1| ≤ mesh) :
    k.node.side = stateSide y.1 ∧
      |Real.log k.node.gap-Real.log (gapValue v y)| ≤ d+4*mesh := by
  obtain ⟨p,hp,rfl⟩ := hfollow
  have hrg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hnext := terminal_valid hs (h.append p hp).admissible
  constructor
  · rw [History.append_node]
    change h.node.side.flip = stateSide y.1
    rw [hcont.2,hside]
  · have hy : y = (y.1,z.2+cost (stateRatio y.1)) := Prod.ext rfl hcont.1
    have hygap : gapValue v y = nextGap (gapValue v z) (stateRatio y.1) := by
      calc
        _ = gapValue v (y.1,z.2+cost (stateRatio y.1)) := congrArg (gapValue v) hy
        _ = _ := gapValue_update v z y.1
    rw [prime_step_gap hell hr hs, hygap]
    exact log_gap_step hrg (Real.exp_pos _) (PrimeTiltBounds.valid_ge_half hnext)
      (CostPrefixTransport.stateRatio_ge_half y.1) hgap hmatch

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
