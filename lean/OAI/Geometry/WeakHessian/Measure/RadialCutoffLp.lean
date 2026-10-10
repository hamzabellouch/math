import Mathlib
import OAI.Geometry.WeakHessian.Measure.RadialCutoff
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_of_memLp_mul_exp {V f : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m) : Integrable f m := by
  apply (hf.integrable_mul hV).congr
  exact ae_of_all _ fun x => by
    change (f x*Real.exp (V x))*Real.exp (-V x) = f x
    rw [mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

lemma integral_cutoff_le_weighted {V f η : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hη : AEStronglyMeasurable η m) (hη1 : ∀ᵐ x ∂m, |η x| ≤ 1) :
    ‖∫ x, f x*η x ∂m‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*‖hV.toLp (fun x => Real.exp (-V x))‖ := by
  have hW : MemLp (fun x => Real.exp (-V x)*η x) 2 m := memLp_mul_bounded hV hη hη1
  let U := hf.toLp (fun x => f x*Real.exp (V x))
  let W := hW.toLp (fun x => Real.exp (-V x)*η x)
  let D := hV.toLp (fun x => Real.exp (-V x))
  have he : (∫ x, f x*η x ∂m) = ⟪U,W⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hW.coeFn_toLp] with x hu hw
    dsimp only [U,W]
    rw [hu,hw]
    simp only [RCLike.inner_apply,conj_trivial]
    calc f x*η x = f x*(Real.exp (V x)*Real.exp (-V x))*η x := by
           rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
         _ = _ := by ring
  have hnorm : ‖W‖ ≤ ‖D‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hW.coeFn_toLp,hV.coeFn_toLp,hη1] with x hx hy hηx
    dsimp only [W,D]
    rw [hx,hy]
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hηx
  rw [he]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_radialCutoff_tendsto (o : X) {f : X → ℝ} (hf : Integrable f m) :
    Tendsto (fun n => ∫ x, f x*radialCutoff o n x ∂m) atTop (𝓝 (∫ x,f x ∂m)) := by
  have H := tendsto_integral_of_dominated_convergence (fun x => |f x|)
    (fun n => hf.aestronglyMeasurable.mul (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
    (by simpa only [Real.norm_eq_abs] using hf.norm)
    (fun n => ae_of_all _ fun x => by
      change |f x*radialCutoff o n x| ≤ |f x|
      rw [abs_mul,abs_of_nonneg (radialCutoff_nonneg o n x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_le_one o n x))
    (ae_of_all _ fun x => tendsto_const_nhds.mul (radialCutoff_tendsto o x))
  simpa only [Pi.mul_apply,mul_one] using H

noncomputable def radialCutoffLp (hfinite : FiniteOnBoundedSets m) (o : X) (n : ℕ) : Lp ℝ 2 m :=
  (sobolev_of_lipschitz_compactSupport hfinite (radialCutoff_lipschitz o n)
    (radialCutoff_compact o n)).1.toLp (radialCutoff o n)
lemma radialCutoffLp_ae (hfinite : FiniteOnBoundedSets m) (o : X) (n : ℕ) :
    radialCutoffLp hfinite o n =ᵐ[m] radialCutoff o n := MemLp.coeFn_toLp _
lemma integral_radialCutoff_eq_inner (hfinite : FiniteOnBoundedSets m) (o : X) (n : ℕ) (f : Lp ℝ 2 m) :
    (∫ x, f x*radialCutoff o n x ∂m) = ⟪radialCutoffLp hfinite o n,f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radialCutoffLp_ae hfinite o n] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
end WeakHessian

end
end InlinedFile0

end OAI
