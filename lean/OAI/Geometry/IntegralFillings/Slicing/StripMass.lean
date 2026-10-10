import Mathlib

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace SharpIntegralFillings.Slicing
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  {u : X → ℝ}
noncomputable def stripMass (u : X → ℝ) (a : ℝ≥0) (t : ℝ) : ℝ≥0∞ :=
  (a:ℝ≥0∞) * μ {x | t ≤ u x ∧ u x ≤ t+(a:ℝ)⁻¹}

lemma measurable_stripMass (hu : Measurable u) (a : ℝ≥0) :
    Measurable (stripMass μ u a) := by
  have hset : MeasurableSet {p : ℝ × X | p.1 ≤ u p.2 ∧ u p.2 ≤ p.1+(a:ℝ)⁻¹} :=
    (measurableSet_le measurable_fst (hu.comp measurable_snd)).inter
      (measurableSet_le (hu.comp measurable_snd) (measurable_fst.add_const _))
  let f : ℝ → X → ℝ≥0∞ := fun t x =>
    if t ≤ u x ∧ u x ≤ t+(a:ℝ)⁻¹ then (a:ℝ≥0∞) else 0
  have hf : Measurable (Function.uncurry f) := by
    exact Measurable.ite hset measurable_const measurable_const
  have heq : stripMass μ u a = fun t => ∫⁻ x, f t x ∂μ := by
    funext t
    have h : MeasurableSet {x | t ≤ u x ∧ u x ≤ t+(a:ℝ)⁻¹} :=
      (measurableSet_le measurable_const hu).inter
      (measurableSet_le hu measurable_const)
    simpa only [stripMass,Set.indicator_apply,Set.mem_ofPred_eq,lintegral_const,
      Measure.restrict_apply_univ,f] using
      (lintegral_indicator h (fun _ => (a:ℝ≥0∞))).symm
  rw [heq]
  exact hf.lintegral_prod_right

lemma lintegral_stripMass (hu : Measurable u) {a : ℝ≥0} (ha : 0 < a) :
    ∫⁻ t : ℝ, stripMass μ u a t = μ univ := by
  have hset : MeasurableSet {p : ℝ × X | p.1 ≤ u p.2 ∧ u p.2 ≤ p.1+(a:ℝ)⁻¹} :=
    (measurableSet_le measurable_fst (hu.comp measurable_snd)).inter
      (measurableSet_le (hu.comp measurable_snd) (measurable_fst.add_const _))
  let f : ℝ → X → ℝ≥0∞ := fun t x =>
    if t ≤ u x ∧ u x ≤ t+(a:ℝ)⁻¹ then (a:ℝ≥0∞) else 0
  have hf : Measurable (Function.uncurry f) :=
    Measurable.ite hset measurable_const measurable_const
  have heq : ∀ t, stripMass μ u a t = ∫⁻ x, f t x ∂μ := by
    intro t
    have h : MeasurableSet {x | t ≤ u x ∧ u x ≤ t+(a:ℝ)⁻¹} :=
      (measurableSet_le measurable_const hu).inter
      (measurableSet_le hu measurable_const)
    simpa only [stripMass,Set.indicator_apply,Set.mem_ofPred_eq,lintegral_const,
      Measure.restrict_apply_univ,f] using
      (lintegral_indicator h (fun _ => (a:ℝ≥0∞))).symm
  simp_rw [heq]
  rw [lintegral_lintegral_swap hf.aemeasurable]
  have ht : ∀ x, ∫⁻ t : ℝ, f t x = 1 := by
    intro x
    have heq' : (fun t => f t x) = (Icc (u x-(a:ℝ)⁻¹) (u x)).indicator (fun _ => (a:ℝ≥0∞)) := by
      funext t
      have hequiv : (t ≤ u x ∧ u x ≤ t+(a:ℝ)⁻¹) ↔
          t ∈ Icc (u x-(a:ℝ)⁻¹) (u x) := by
        simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
      simp only [f,Set.indicator_apply,hequiv]
    rw [heq',lintegral_indicator measurableSet_Icc,lintegral_const,Measure.restrict_apply_univ,
      Real.volume_Icc]
    simp only [sub_sub_cancel]
    rw [ENNReal.ofReal_inv_of_pos (show 0 < (a:ℝ) from ha),ENNReal.ofReal_coe_nnreal]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast ne_of_gt ha) ENNReal.coe_ne_top
  simp_rw [ht]
  simp

lemma ae_finite_strip_liminf (hu : Measurable u) :
    ∀ᵐ t : ℝ, liminf (fun n : ℕ => stripMass μ u ((n:ℝ≥0)+1) t) atTop < (⊤ : ℝ≥0∞) := by
  have hmeas := fun n : ℕ => measurable_stripMass μ hu ((n:ℝ≥0)+1)
  have hbound : (∫⁻ t : ℝ, liminf (fun n : ℕ => stripMass μ u ((n:ℝ≥0)+1) t) atTop) ≤ μ univ := by
    have h := lintegral_liminf_le (μ := volume) (u := atTop) hmeas
    have hi : ∀ n : ℕ, ∫⁻ t : ℝ, stripMass μ u ((n:ℝ≥0)+1) t = μ univ :=
      fun n => lintegral_stripMass μ hu (by positivity)
    simpa only [hi,liminf_const] using h
  exact ae_lt_top (Measurable.liminf hmeas) (ne_top_of_le_ne_top (measure_ne_top μ univ) hbound)

lemma ae_bounded_strip_subsequence (hu : Measurable u) :
    ∀ᵐ t : ℝ, ∃ (j : ℕ → ℕ) (M : ℝ≥0), Tendsto j atTop atTop ∧
      ∀ n, stripMass μ u ((j n:ℝ≥0)+1) t ≤ M := by
  filter_upwards [ae_finite_strip_liminf μ hu] with t ht
  let r := liminf (fun n : ℕ => stripMass μ u ((n:ℝ≥0)+1) t) atTop
  let M : ℝ≥0 := r.toNNReal+1
  have hr : r < (M:ℝ≥0∞) := by
    change r < ((r.toNNReal+1:ℝ≥0):ℝ≥0∞)
    rw [ENNReal.coe_add,ENNReal.coe_toNNReal ht.ne]
    exact ENNReal.lt_add_right ht.ne (by simp)
  have hf := frequently_lt_of_liminf_lt (u := fun n : ℕ => stripMass μ u ((n:ℝ≥0)+1) t) (h := hr)
  choose j hj hbound using frequently_atTop.mp hf
  refine ⟨j,M,?_,fun n => (hbound n).le⟩
  exact tendsto_atTop_mono hj tendsto_id

end SharpIntegralFillings.Slicing

end

end OAI
