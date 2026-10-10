import Mathlib
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smooth_direction_integral_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) (f : SmoothScalar E) (hf : HasCompactSupport f.val) :
    (∫ x, (smoothDirection v f).val x ∂μ) = 0 := by
  have hh := smooth_integration_by_parts μ v f (1 : SmoothScalar E) hf
  simpa using hh

lemma compact_flux_mean_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] (F : Coord3 → Coord3)
    (hdiv : ∀ ψ : Coord3 → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0) (i : Fin 3) :
    (∫ x, F x i ∂μ) = 0 := by
  let L : Coord3 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hh := hdiv L L.contDiff
  simpa only [L.fderiv, L, ContinuousLinearMap.proj_apply] using hh

lemma pairing_bound_of_zero_mean
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (f φ : E → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : Continuous φ) (hmean : (∫ x, f x ∂μ) = 0)
    {c ω : ℝ}
    (hosc : ∀ x ∈ tsupport f, |φ x - c| ≤ ω) :
    |∫ x, φ x * f x ∂μ| ≤ ω * ∫ x, |f x| ∂μ := by
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have h1 : Integrable (fun x => φ x * f x) μ :=
    (hφ.mul hf).integrable_of_hasCompactSupport hc.mul_left
  have h2 : Integrable (fun x => (φ x-c)*f x) μ :=
    ((hφ.sub continuous_const).mul hf).integrable_of_hasCompactSupport hc.mul_left
  have he : (∫ x, φ x * f x ∂μ) = ∫ x, (φ x-c)*f x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub h1 (hfi.const_mul c), integral_const_mul, hmean, mul_zero, sub_zero]
  rw [he]
  calc
    _ ≤ ∫ x, |(φ x-c)*f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ω * |f x| ∂μ := by
      apply integral_mono_ae h2.abs (hfi.abs.const_mul ω)
      exact Filter.Eventually.of_forall fun x => by
        change |(φ x-c)*f x| ≤ ω * |f x|
        by_cases hx : x ∈ tsupport f
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hosc x hx) (abs_nonneg _)
        · rw [image_eq_zero_of_notMem_tsupport hx]; simp
    _ = _ := integral_const_mul _ _

end ScalarConductivity

end

end OAI
