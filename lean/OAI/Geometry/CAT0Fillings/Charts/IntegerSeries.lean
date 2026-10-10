import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Summation

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma intCast_tsum_exists (a : ℕ → ℤ) :
    ∃ z : ℤ, (z : ℝ) = ∑' i, (a i : ℝ) := by
  by_cases h : Summable (fun i => (a i : ℝ))
  · have hm : (∑' i, (a i : ℝ)) ∈ Set.range ((↑) : ℤ → ℝ) := by
      apply Real.isClosed_range_intCast.mem_of_tendsto h.hasSum
      exact Filter.Eventually.of_forall fun s => ⟨∑ i ∈ s, a i,by simp⟩
    exact hm
  · exact ⟨0,by simpa only [Int.cast_zero] using (tsum_eq_zero_of_not_summable h).symm⟩

noncomputable def summedMultiplicity (θ : ℕ → X → ℤ) (x : X) : ℤ :=
  (intCast_tsum_exists (fun i => θ i x)).choose

omit [MeasurableSpace X] in
lemma summedMultiplicity_cast (θ : ℕ → X → ℤ) (x : X) :
    (summedMultiplicity θ x : ℝ) = ∑' i, (θ i x : ℝ) :=
  (intCast_tsum_exists (fun i => θ i x)).choose_spec

lemma summedMultiplicity_integrable {θ : ℕ → X → ℤ}
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) μ)
    (hS : Summable (fun i => ∫ x, |(θ i x : ℝ)| ∂μ)) :
    Integrable (fun x => (summedMultiplicity θ x : ℝ)) μ := by
  simp_rw [summedMultiplicity_cast]
  exact integrable_series hθ (by simpa only [Real.norm_eq_abs] using hS)

lemma summedMultiplicity_integral_weight {θ : ℕ → X → ℤ}
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) μ)
    (hS : Summable (fun i => ∫ x, |(θ i x : ℝ)| ∂μ))
    {g : X → ℝ} (hg : AEStronglyMeasurable g μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖g x‖ ≤ M) :
    (∫ x, (summedMultiplicity θ x : ℝ) * g x ∂μ) =
      ∑' i, ∫ x, (θ i x : ℝ) * g x ∂μ := by
  have hI i := (hθ i).mul_bdd hg hM
  have hsum : Summable (fun i => ∫ x, ‖(θ i x : ℝ) * g x‖ ∂μ) := by
    apply (hS.mul_left M).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro i
      rw [←integral_const_mul]
      apply integral_mono_ae (hI i).norm ((hθ i).abs.const_mul M)
      filter_upwards [hM] with x hx
      simpa only [norm_mul,Real.norm_eq_abs,mul_comm] using
        mul_le_mul_of_nonneg_left hx (norm_nonneg (θ i x : ℝ))
  rw [integral_tsum_of_summable_integral_norm hI hsum]
  apply integral_congr_ae
  filter_upwards with x
  rw [summedMultiplicity_cast,tsum_mul_right]

end CAT0Fillings

end

end OAI
