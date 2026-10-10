import Mathlib
import OAI.Geometry.CAT0Fillings.Jacobian.Coordinates

namespace OAI

section
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
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
omit [FiniteDimensional ℝ E] in
lemma integrable_continuous_mul_compact_fderiv {u η : E → ℝ}
    (hu : Continuous u) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (v : E) (c : ℝ) :
    Integrable (fun x => u x * c * fderiv ℝ η x v) μ := by
  exact ((hu.mul continuous_const).mul
    ((hη.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hηc.fderiv_apply ℝ v).mul_left

lemma integral_coordinateJacobian_expand {n : ℕ} {u η : E → ℝ}
    {g : Fin n → E → ℝ} (hu : Continuous u) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) {K : ℝ≥0} (hg : ∀ i, LipschitzWith K (g i))
    (v : Fin (n+1) → E) :
    (∫ x, u x * coordinateJacobian (Fin.cons η g) v x ∂μ) =
      ∑ i : Fin (n+1), ∫ x, (u x * (-1 : ℝ)^i.val * fderiv ℝ η x (v i)) *
        coordinateJacobian g (i.removeNth v) x ∂μ := by
  simp_rw [coordinateJacobian_cons, Finset.mul_sum]
  have heq (x : E) (i : Fin (n+1)) :
      u x * ((-1 : ℝ)^i.val * fderiv ℝ η x (v i) * coordinateJacobian g (i.removeNth v) x) =
        (u x * (-1 : ℝ)^i.val * fderiv ℝ η x (v i)) * coordinateJacobian g (i.removeNth v) x := by ring
  simp_rw [heq]
  exact integral_finsetSum _ (fun i _ => integrable_mul_coordinateJacobian μ
    (integrable_continuous_mul_compact_fderiv μ hu hη hηc (v i) _) hg (i.removeNth v))

omit [IsAddHaarMeasure μ] in
lemma integral_weight_coordinateJacobian_difference_bound {n : ℕ} {a b : E → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) {f : Fin n → E → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (v : Fin n → E) {B : ℝ}
    (hB : ∀ x, ‖coordinateJacobian f v x‖ ≤ B) :
    ‖(∫ x, a x * coordinateJacobian f v x ∂μ) -
      (∫ x, b x * coordinateJacobian f v x ∂μ)‖ ≤
        (∫ x, ‖a x-b x‖ ∂μ) * B := by
  rw [← integral_sub (integrable_mul_coordinateJacobian μ ha hf v)
    (integrable_mul_coordinateJacobian μ hb hf v)]
  simp_rw [← sub_mul]
  calc ‖∫ x, (a x - b x) * coordinateJacobian f v x ∂μ‖ ≤
      ∫ x, ‖a x-b x‖ * B ∂μ := by
        refine norm_integral_le_of_norm_le ((ha.sub hb).norm.mul_const B) ?_
        filter_upwards with x
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    _ = _ := integral_mul_const B _

end CAT0Fillings

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

lemma integrable_coordinateJacobian_cons_weight {n : ℕ} {u η : E → ℝ}
    {g : Fin n → E → ℝ} (hu : Continuous u) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) {K : ℝ≥0} (hg : ∀ i, LipschitzWith K (g i))
    (v : Fin (n+1) → E) :
    Integrable (fun x => u x * coordinateJacobian (Fin.cons η g) v x) μ := by
  have H := integrable_finsetSum (s := Finset.univ) (fun i _ =>
    integrable_mul_coordinateJacobian μ
      (integrable_continuous_mul_compact_fderiv μ hu hη hηc (v i) ((-1 : ℝ)^i.val)) hg (i.removeNth v))
  apply H.congr
  filter_upwards with x
  symm
  simp only [coordinateJacobian_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma tendsto_integral_coordinateJacobian_head_error {n : ℕ} {η u : E → ℝ}
    {us : ℕ → E → ℝ} {gs : ℕ → Fin n → E → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {K : ℝ≥0}
    (hu : LipschitzWith K u) (hus : ∀ j, LipschitzWith K (us j))
    (hgs : ∀ j i, LipschitzWith K (gs j i))
    (hulim : ∀ x, Tendsto (fun j => us j x) atTop (𝓝 (u x)))
    (v : Fin (n+1) → E) :
    Tendsto (fun j => ∫ x, (us j x-u x) * coordinateJacobian (Fin.cons η (gs j)) v x ∂μ)
      atTop (𝓝 0) := by
  classical
  obtain ⟨N, hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hηc hη one_ne_zero
  obtain ⟨B, _, hB⟩ := coordinateJacobian_uniform_bound (max N K) v
  obtain ⟨C, hC0, hC⟩ := uniformly_bounded_lipschitz_on_compact hus (hulim 0) hηc
  have hCu (x : E) (hx : x ∈ tsupport η) : ‖u x‖ ≤ C :=
    le_of_tendsto' (hulim x).norm (fun j => hC j x hx)
  let A := (tsupport η).indicator (fun _ : E => 2*C)
  let as := fun j => (tsupport η).indicator (fun x => us j x-u x)
  have hA : Integrable A μ := (integrable_indicator_iff (isClosed_tsupport η).measurableSet).2
    (continuous_const.continuousOn.integrableOn_compact hηc)
  have ha (j : ℕ) : AEStronglyMeasurable (as j) μ :=
    ((hus j).continuous.sub hu.continuous).aestronglyMeasurable.indicator
      (isClosed_tsupport η).measurableSet
  have haA (j : ℕ) : ∀ᵐ x ∂μ, ‖as j x‖ ≤ A x := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · simp only [as, A, indicator_of_mem hx]
      calc ‖us j x-u x‖ ≤ ‖us j x‖ + ‖u x‖ := norm_sub_le _ _
        _ ≤ 2*C := by linarith [hC j x hx, hCu x hx]
    · simp [as, A, hx]
  have halim : ∀ᵐ x ∂μ, Tendsto (fun j => as j x) atTop (𝓝 0) := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · simpa [as, hx] using (hulim x).sub_const (u x)
    · simp [as, hx]
  have hJ (j : ℕ) : ∀ x, ‖coordinateJacobian (Fin.cons η (gs j)) v x‖ ≤ B := by
    apply hB
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hN.weaken (le_max_left _ _)
    · exact (hgs j i).weaken (le_max_right _ _)
  have H := tendsto_integral_mul_uniformly_bounded μ hA ha
    (fun j => (measurable_coordinateJacobian (Fin.cons η (gs j)) v).aestronglyMeasurable)
    haA hJ halim
  convert H using 1
  funext j
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport η
  · simp [as, hx]
  · simp [as, hx, coordinateJacobian_cons, fderiv_of_notMem_tsupport ℝ hx]

end CAT0Fillings

end

end OAI
