import Mathlib
import OAI.Geometry.CAT0Fillings.Jacobian.HeadEstimates

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
lemma coordinateJacobian_weak_from_smooth {n : ℕ} {fs : ℕ → Fin n → E → ℝ}
    {f : Fin n → E → ℝ} {K : ℝ≥0} (hfs : ∀ j i, LipschitzWith K (fs j i))
    (hf : ∀ i, LipschitzWith K (f i)) (v : Fin n → E)
    (hsm : ∀ η : E → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      Tendsto (fun j => ∫ x, η x * coordinateJacobian (fs j) v x ∂μ) atTop
        (𝓝 (∫ x, η x * coordinateJacobian f v x ∂μ)))
    {a : E → ℝ} (ha : Integrable a μ) :
    Tendsto (fun j => ∫ x, a x * coordinateJacobian (fs j) v x ∂μ) atTop
      (𝓝 (∫ x, a x * coordinateJacobian f v x ∂μ)) := by
  obtain ⟨B, hB0, hB⟩ := coordinateJacobian_uniform_bound K v
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hd : 0 < 4*B+1 := by positivity
  obtain ⟨η, hη, hηc, happrox⟩ := integrable_smooth_compact_L1_approx μ ha (div_pos hε hd)
  have hηI : Integrable η μ := hη.continuous.integrable_of_hasCompactSupport hηc
  have hbε : (ε / (4*B+1))*B < ε/4 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith
  have hdist (q : Fin n → E → ℝ) (hq : ∀ i, LipschitzWith K (q i)) :
      dist (∫ x, a x * coordinateJacobian q v x ∂μ)
        (∫ x, η x * coordinateJacobian q v x ∂μ) < ε/4 := by
    rw [dist_eq_norm]
    exact ((integral_weight_coordinateJacobian_difference_bound μ ha hηI hq v (hB q hq)).trans
      (mul_le_mul_of_nonneg_right happrox hB0)).trans_lt hbε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hsm η hη hηc) (ε/2) (half_pos hε)
  refine ⟨N, fun j hj => ?_⟩
  have H₁ := dist_triangle
    (∫ x, a x * coordinateJacobian (fs j) v x ∂μ)
    (∫ x, η x * coordinateJacobian (fs j) v x ∂μ)
    (∫ x, a x * coordinateJacobian f v x ∂μ)
  have H₂ := dist_triangle
    (∫ x, η x * coordinateJacobian (fs j) v x ∂μ)
    (∫ x, η x * coordinateJacobian f v x ∂μ)
    (∫ x, a x * coordinateJacobian f v x ∂μ)
  have H₃ := hdist (fs j) (hfs j)
  have H₄ := hdist f hf
  rw [dist_comm] at H₄
  have H₅ := hN j hj
  linarith

end CAT0Fillings

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

lemma weak_coordinateJacobian (n : ℕ) :
    ∀ {K : ℝ≥0} {fs : ℕ → Fin n → E → ℝ} {f : Fin n → E → ℝ},
    (∀ j i, LipschitzWith K (fs j i)) → (∀ i, LipschitzWith K (f i)) →
    (∀ i x, Tendsto (fun j => fs j i x) atTop (𝓝 (f i x))) →
    ∀ (v : Fin n → E) {a : E → ℝ}, Integrable a μ →
    Tendsto (fun j => ∫ x, a x * coordinateJacobian (fs j) v x ∂μ) atTop
      (𝓝 (∫ x, a x * coordinateJacobian f v x ∂μ)) := by
  induction n with
  | zero =>
    intro K fs f hfs hf hlim v a ha
    simp [coordinateJacobian]
  | succ n ih =>
    intro K fs f hfs hf hlim v a ha
    apply coordinateJacobian_weak_from_smooth μ hfs hf v ?_ ha
    intro η hη hηc
    have HE := tendsto_integral_coordinateJacobian_head_error μ hη hηc
      (hf 0) (fun j => hfs j 0) (fun j i => hfs j i.succ) (hlim 0) v
    have HF : Tendsto
        (fun j => ∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) atTop
        (𝓝 (∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => f i.succ)) v x ∂μ)) := by
      have heq (j : ℕ) := integral_coordinateJacobian_expand μ (hf 0).continuous hη hηc
        (fun i => hfs j i.succ) v
      have hleq := integral_coordinateJacobian_expand μ (hf 0).continuous hη hηc
        (fun i => hf i.succ) v
      simp_rw [heq, hleq]
      apply tendsto_finsetSum
      intro i _
      exact ih (fun j k => hfs j k.succ) (fun k => hf k.succ) (fun k x => hlim k.succ x)
        (i.removeNth v) (integrable_continuous_mul_compact_fderiv μ
          (hf 0).continuous hη hηc (v i) ((-1 : ℝ)^i.val))
    have heq (j : ℕ) :
        (∫ x, (fs j 0 x-f 0 x) * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) =
        (∫ x, fs j 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) -
        (∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) := by
      simpa only [← sub_mul] using integral_sub
        (integrable_coordinateJacobian_cons_weight μ (hfs j 0).continuous hη hηc
          (fun i => hfs j i.succ) v)
        (integrable_coordinateJacobian_cons_weight μ (hf 0).continuous hη hηc
          (fun i => hfs j i.succ) v)
    simp_rw [heq] at HE
    have HI : Tendsto
        (fun j => ∫ x, fs j 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) atTop
        (𝓝 (∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => f i.succ)) v x ∂μ)) := by
      simpa only [sub_add_cancel, zero_add] using HE.add HF
    have hcons (q : Fin (n+1) → E → ℝ) : Fin.cons (q 0) (fun i => q i.succ) = q := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    have hleft (j : ℕ) : (∫ x, η x * coordinateJacobian (fs j) v x ∂μ) =
        -(∫ x, fs j 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) := by
      simpa only [hcons] using integral_coordinateJacobian_cons μ hη hηc
        (hfs j 0) (fun i => hfs j i.succ) v
    have hright : (∫ x, η x * coordinateJacobian f v x ∂μ) =
        -(∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => f i.succ)) v x ∂μ) := by
      simpa only [hcons] using integral_coordinateJacobian_cons μ hη hηc
        (hf 0) (fun i => hf i.succ) v
    simp_rw [hleft, hright]
    exact HI.neg

end CAT0Fillings

open Set Filter Metric
open scoped Topology NNReal

end

end OAI
