import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.ChainRule

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
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

namespace CAT0Fillings
open Set MeasureTheory Filter BorelCoefficients Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  {k : ℕ} {T : Functional X (k+1)}
lemma contractCurrent_comp_controls (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {u : X → ℝ} (hu : BoundedLip u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    {E : Set X} (hE : MeasurableSet E) {D : ℝ≥0}
    (hD : ∀ x, |dφ (u x)| ≤ D) (hzero : ∀ x ∉ E, dφ (u x) = 0) :
    Controls (contractCurrent (φ ∘ u) T) ((K*D) • μ.restrict E) := by
  intro b π hb hπ
  have hπ' : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (Matrix.vecCons u π i) :=
    fun i => Fin.cases hu.1 (fun j => ⟨1,hπ j⟩) i
  rw [contractCurrent_apply _ _ ⟨hb,fun i => ⟨1,hπ i⟩⟩,
    integral_smul_nnreal_measure]
  have heq := Foundations.IntegerRectifiable.apply_update_comp hrect hb hu hφ hφu hdu
    (Matrix.vecCons u π) hπ' 0
  simp only [vecCons_update_head] at heq
  rw [heq]
  have hbound := hT.mass_bound hμ (hb.mul hdu) (Matrix.vecCons K (fun _ => 1))
    (show ∀ i, LipschitzWith (Matrix.vecCons K (fun _ => 1) i) (Matrix.vecCons u π i) from
      fun i => Fin.cases hK (fun j => hπ j) i)
  have hib := (integrable_boundedLip μ hb).abs
  have hid := (integrable_boundedLip μ (hb.mul hdu)).abs
  have hi : (∫ x, |b x*dφ (u x)| ∂μ) ≤ (D:ℝ) * ∫ x in E, |b x| ∂μ := by
    rw [←integral_indicator hE,←integral_const_mul]
    apply integral_mono_ae hid ((hib.indicator hE).const_mul D)
    filter_upwards [] with x
    by_cases hx : x ∈ E
    · simp only [indicator_of_mem hx,abs_mul]
      simpa only [Function.comp_apply,mul_comm] using
        mul_le_mul_of_nonneg_left (hD x) (abs_nonneg (b x))
    · simp [indicator_of_notMem hx,hzero x hx]
  calc
    |T (fun x => b x*dφ (u x)) (Matrix.vecCons u π)| ≤
        (K:ℝ)*(∫ x, |b x*dφ (u x)| ∂μ) := by
      simpa [Fin.prod_univ_succ] using hbound
    _ ≤ (K:ℝ)*((D:ℝ)*∫ x in E, |b x| ∂μ) := mul_le_mul_of_nonneg_left hi K.coe_nonneg
    _ = (K*D) • ∫ x, |b x| ∂μ.restrict E := by
      simp only [NNReal.smul_def,NNReal.coe_mul]
      ring

lemma weightedCurrent_comp_boundary_controls (hT : IsMetricCurrent T)
    (hrect : IntegerRectifiable T) (hz : IsCycle T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {u : X → ℝ} (hu : BoundedLip u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    {E : Set X} (hE : MeasurableSet E) {D : ℝ≥0}
    (hD : ∀ x, |dφ (u x)| ≤ D) (hzero : ∀ x ∉ E, dφ (u x) = 0) :
    Controls (boundarySucc (weightedCurrent μ hT (φ ∘ u))) ((K*D) • μ.restrict E) := by
  rw [weightedCurrent_boundary_cycle hT hrect hz μ hμ hφu]
  intro b π hb hπ
  simpa only [Pi.neg_apply,abs_neg] using
    contractCurrent_comp_controls hT hrect μ hμ hu hK hφ hφu hdu hE hD hzero b π hb hπ

end CAT0Fillings

open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
