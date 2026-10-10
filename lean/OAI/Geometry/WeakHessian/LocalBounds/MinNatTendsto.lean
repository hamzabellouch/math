import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ExpMulLp
import OAI.Geometry.WeakHessian.Calculus.IntegralSqFatou

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

lemma min_nat_tendsto (v : ℝ) : Tendsto (fun n : ℕ => min v (n:ℝ)) atTop (𝓝 v) := by
  obtain ⟨k,hk⟩ := exists_nat_ge v
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (min_eq_left (hk.trans (by exact_mod_cast hn))).symm

lemma expMulLp_norm_le_weighted {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    (u : Lp ℝ 2 m) (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (n : ℕ) :
    ‖expMulLp ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
        (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u‖ ≤
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [expMulLp_ae ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u,hU.coeFn_toLp] with x hx hy
  rw [hx,hy]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (min_le_left _ _)) (abs_nonneg _)

lemma memLp_mul_exp_of_trunc {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    (u : Lp ℝ 2 m) {B : ℝ}
    (hB : ∀ n : ℕ, ‖expMulLp ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
      (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u‖^2 ≤ B) :
    MemLp (fun x => u x*Real.exp (V x)) 2 m ∧
      (∫ x, (u x*Real.exp (V x))^2 ∂m) ≤ B := by
  let fs : ℕ → X → ℝ := fun n x => u x*Real.exp (min (V x) (n:ℝ))
  have hfs (n : ℕ) : MemLp (fs n) 2 m := by
    exact MemLp.ae_eq (expMulLp_ae _ _ _) (Lp.memLp (expMulLp ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
      (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u))
  apply integral_sq_fatou ((Lp.aestronglyMeasurable u).mul
    (Real.continuous_exp.comp_aestronglyMeasurable hV)) hfs
  · exact ae_of_all _ fun x => tendsto_const_nhds.mul
      ((Real.continuous_exp.tendsto _).comp (min_nat_tendsto (V x)))
  · intro n
    have H := hB n
    rw [expMulLp_norm_sq] at H
    convert H using 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp only [fs,mul_pow,sq_exp_eq]

end WeakHessian

end
end InlinedFile0

end OAI
