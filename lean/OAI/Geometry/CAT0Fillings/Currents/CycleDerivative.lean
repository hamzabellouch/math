import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.MovingAction
import OAI.Geometry.CAT0Fillings.Currents.CycleDifference

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)
omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma bounded_time_slope {d : ℕ} (V : ℝ → Fin d → BL) (K : ℝ≥0)
    (ht : ∀ i x, LipschitzWith K (fun t => (V t i : X → ℝ) x)) (t h : ℝ) (i : Fin d) (x : X) :
    |h⁻¹ * ((V (t+h) i : X → ℝ) x - (V t i : X → ℝ) x)| ≤ K := by
  by_cases hh : h=0
  · simp [hh]
  · have H := (ht i x).dist_le_mul (t+h) t
    rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left] at H
    rw [abs_mul,abs_inv]
    calc |h|⁻¹ * |(V (t+h) i : X → ℝ) x - (V t i : X → ℝ) x| ≤
      |h|⁻¹ * ((K:ℝ)*|h|) := mul_le_mul_of_nonneg_left H (by positivity)
      _ = K := by field_simp

lemma IsMetricCurrent.hasDeriv_cycle_path {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    (V : ℝ → Fin (k+2) → BL) (K : ℝ≥0)
    (hx : ∀ t i, LipschitzWith K (V t i : X → ℝ))
    (ht : ∀ i x, LipschitzWith K (fun t => (V t i : X → ℝ) x))
    (t : ℝ) (D : Fin (k+2) → X → ℝ) (hD : ∀ i, Integrable (D i) μ)
    (hder : ∀ i, ∀ᵐ x ∂μ, HasDerivAt (fun s => (V s i : X → ℝ) x) (D i x) t) :
    HasDerivAt (fun s => hcur.fullMultilinear (V s))
      (∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur (D i)
        (fun j => (i.removeNth (V t) j : X → ℝ))) t := by
  let B (h : ℝ) (i : Fin (k+2)) : BL := h⁻¹ • (V (t+h) i - V t i)
  let P (h : ℝ) (i : Fin (k+2)) : Fin (k+1) → X → ℝ :=
    fun j => (i.removeNth (mixedTuple (V (t+h)) (V t) i) j : X → ℝ)
  have hP (h i j) : LipschitzWith K (P h i j) := by
    dsimp [P,Fin.removeNth,mixedTuple]
    split_ifs <;> exact hx _ _
  have hPb (i j x) : Tendsto (fun h => P h i j x) (𝓝[≠] 0)
      (𝓝 ((i.removeNth (V t) j : X → ℝ) x)) := by
    dsimp [P,Fin.removeNth,mixedTuple]
    split_ifs
    · have H : Tendsto (fun h : ℝ => (V (t+h) (i.succAbove j) : X → ℝ) x) (𝓝 0)
          (𝓝 ((V t (i.succAbove j) : X → ℝ) x)) := by
        have HH : Tendsto (fun h : ℝ => t+h) (𝓝 0) (𝓝 t) := by
          simpa only [add_zero] using (tendsto_const_nhds.add tendsto_id :
            Tendsto (fun h : ℝ => t+h) (𝓝 0) (𝓝 (t+0)))
        exact (ht (i.succAbove j) x).continuous.continuousAt.tendsto.comp HH
      simpa only [add_zero] using H.mono_left nhdsWithin_le_nhds
    · exact tendsto_const_nhds
  have hbi (h i) : Integrable (B h i : X → ℝ) μ :=
    BorelCoefficients.integrable_boundedLip μ (B h i).property
  have hL1 (i) : Tendsto (fun h => (hbi h i).toL1 (B h i)) (𝓝[≠] 0)
      (𝓝 ((hD i).toL1 (D i))) := by
    apply BorelCoefficients.tendsto_toL1_dominated μ (fun h => hbi h i) (hD i)
      (G := fun _ => (K:ℝ)) (integrable_const (K:ℝ))
    · intro h
      filter_upwards with x
      exact bounded_time_slope V K ht t h i x
    · filter_upwards [hder i] with x hdx
      exact hdx.tendsto_slope_zero
  have hlim (i) : Tendsto (fun h => T (B h i) (P h i)) (𝓝[≠] 0)
      (𝓝 (BorelCoefficients.borelAction μ hcur (D i)
        (fun j => (i.removeNth (V t) j : X → ℝ)))) := by
    have H := BorelCoefficients.borelAction_moving μ hcur hμ (fun h => hbi h i) (hD i)
      (hL1 i) _ (fun h => P h i) (fun j => ⟨K,fun h => hP h i j⟩) (hPb i)
    have heq (h : ℝ) := BorelCoefficients.borelAction_eq μ hcur hμ
      (show Admissible (B h i : X → ℝ) (P h i) from
        ⟨(B h i).property,fun j => ⟨K,hP h i j⟩⟩)
    simp_rw [heq] at H
    exact H
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have H := tendsto_finsetSum Finset.univ (fun i _ => (hlim i).const_mul ((-1:ℝ)^i.val))
  convert H using 1
  funext h
  simp only [smul_eq_mul,hcur.cycle_difference hT hz,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc := hcur.linearFirst (V (t+h) i - V t i) (V (t+h) i - V t i)
    (P h i) h⁻¹ 0 (V (t+h) i - V t i).property (V (t+h) i - V t i).property
    (fun j => ⟨K,hP h i j⟩)
  simp only [zero_mul,add_zero] at hc
  change h⁻¹ * ((-1:ℝ)^i.val * T (V (t+h) i - V t i) (P h i)) =
    (-1:ℝ)^i.val * T (B h i) (P h i)
  rw [show T (B h i) (P h i) = h⁻¹ * T (V (t+h) i - V t i) (P h i) from hc]
  ring

end CAT0Fillings

open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

end
end

end OAI
