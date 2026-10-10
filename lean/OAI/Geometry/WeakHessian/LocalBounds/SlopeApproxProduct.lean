import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApproxAntitone

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


namespace WeakHessian
open Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

lemma slopeApprox_product_le {f g : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : X) :
    slopeApprox (fun y => f y*g y) n x ≤
      ENNReal.ofReal (|f x|+(L:ℝ)/(n+1))*slopeApprox g n x+
        ENNReal.ofReal |g x| * slopeApprox f n x := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hfx : |f y| ≤ |f x|+(L:ℝ)/(n+1) := by
    calc
      |f y| ≤ |f x|+|f y-f x| := by
        convert abs_add_le (f x) (f y-f x) using 1
        congr 1
        ring
      _ ≤ |f x|+(L:ℝ)*dist y x := add_le_add (le_refl _)
        (by simpa only [Real.dist_eq] using hf.dist_le_mul y x)
      _ ≤ _ := by
        apply add_le_add (le_refl _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hy.le L.coe_nonneg
  have hreal : |f y*g y-f x*g x|/dist y x ≤
      (|f x|+(L:ℝ)/(n+1))*(|g y-g x|/dist y x)+
        |g x| * (|f y-f x|/dist y x) := by
    calc _ = |f y*(g y-g x)+g x*(f y-f x)|/dist y x := by congr 2; ring
      _ ≤ (|f y| * |g y-g x|+|g x| * |f y-f x|)/dist y x := by
        apply div_le_div_of_nonneg_right _ dist_nonneg
        simpa only [abs_mul] using abs_add_le (f y*(g y-g x)) (g x*(f y-f x))
      _ = |f y| * (|g y-g x|/dist y x)+|g x| * (|f y-f x|/dist y x) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ENNReal.ofReal ((|f x|+(L:ℝ)/(n+1))*(|g y-g x|/dist y x)+
        |g x| * (|f y-f x|/dist y x)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (|f x|+(L:ℝ)/(n+1))*ENNReal.ofReal (|g y-g x|/dist y x)+
        ENNReal.ofReal |g x| * ENNReal.ofReal (|f y-f x|/dist y x) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ _ := add_le_add
      (mul_le_mul' le_rfl (show ENNReal.ofReal (|g y-g x|/dist y x) ≤ slopeApprox g n x from le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
      (mul_le_mul' le_rfl (show ENNReal.ofReal (|f y-f x|/dist y x) ≤ slopeApprox f n x from le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

lemma localSlope_product_le {f g : X → ℝ} {L T : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith T g) (x : X) :
    localSlope (fun y => f y*g y) x ≤ ENNReal.ofReal |f x| * localSlope g x+
      ENNReal.ofReal |g x| * localSlope f x := by
  have hf0 : localSlope f x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)
  have hg0 : localSlope g x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_lipschitz hg x)
  have ht (u : X → ℝ) : Tendsto (fun n : ℕ => slopeApprox u n x) atTop (𝓝 (localSlope u x)) := by
    rw [localSlope_eq_iInf_slopeApprox]
    exact tendsto_atTop_iInf (slopeApprox_antitone u x)
  have hfac : Tendsto (fun n : ℕ => ENNReal.ofReal (|f x|+(L:ℝ)/(n+1))) atTop
      (𝓝 (ENNReal.ofReal |f x|)) := by
    have H := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (L:ℝ) |>.const_add |f x|
    simp only [mul_zero,add_zero] at H
    simpa only [mul_one_div,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp H
  apply ge_of_tendsto' ((ENNReal.Tendsto.mul hfac (Or.inr hg0) (ht g)
    (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.mul (tendsto_const_nhds (x := ENNReal.ofReal |g x|)) (Or.inr hf0) (ht f)
        (Or.inr ENNReal.ofReal_ne_top)))
  intro n
  rw [localSlope_eq_iInf_slopeApprox (fun y => f y*g y)]
  exact (iInf_le (fun n : ℕ => slopeApprox (fun y => f y*g y) n x) n).trans
    (slopeApprox_product_le hf n x)
end WeakHessian

end

end OAI
