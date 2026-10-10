import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerResolventDavies
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatDavies
import OAI.Geometry.WeakHessian.Sobolev.Integral
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous
import OAI.Geometry.WeakHessian.Measure.RadialCutoffLp

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
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_laplacian_integral_zero {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t A x ∂m) = 0 := by
  have hUt := (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1
  have hAt := (hcd.cheegerHeat_weighted hfinite o h A hV hA ht).1
  have hpar := hcd.global_localGradientParallelogram hfinite o h
  have hLap := hcd.global_isLaplacian_of_formGenerator hfinite o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  exact hLap.integral_eq_zero hfinite hpar o (integrable_of_memLp_mul_exp hAt hdecay)
    (integrable_of_memLp_mul_exp (hLap.memLp_gradient_mul_exp hfinite hpar hV hUt hAt) hdecay)

lemma CurvatureDimension.cheegerHeat_mass_weighted_generator {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t u x ∂m) = ∫ x, u x ∂m := by
  let C := ‖hA.toLp (fun x => A x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)*
      ‖hdecay.toLp (fun x => Real.exp (-V x))‖
  let fn : ℕ → ℝ → ℝ := fun n s => ∫ x, cheegerHeat h s A x*radialCutoff o n x ∂m
  have hfn (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    have he : fn n = fun s => (innerSL ℝ (radialCutoffLp hfinite o n)) (cheegerHeat h s A) := by
      funext s; exact integral_radialCutoff_eq_inner hfinite o n _
    rw [he]
    exact (innerSL ℝ (radialCutoffLp hfinite o n)).continuous.comp_continuousOn
      (cheegerHeat_continuousOn hfinite h A)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 t) : ‖fn n s‖ ≤ C := by
    have hsW := (hcd.cheegerHeat_weighted hfinite o h A hV hA hs.1).1
    have HH := integral_cutoff_le_weighted hsW hdecay
      (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [abs_of_nonneg (radialCutoff_nonneg o n x)] using radialCutoff_le_one o n x)
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (hcd.cheegerHeat_weighted_norm hfinite o h A hV hA hs.1).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop (𝓝 0) := by
    have H := integral_radialCutoff_tendsto o
      (integrable_of_memLp_mul_exp (hcd.cheegerHeat_weighted hfinite o h A hV hA hs).1 hdecay)
    rw [hcd.cheegerHeat_laplacian_integral_zero hfinite o h hu hV hU hA hdecay hs] at H
    exact H
  have htime : Tendsto (fun n => ∫ s in 0..t, fn n s) atTop (𝓝 0) := by
    have H := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := t) (f := fun _ => (0:ℝ)) (fun _ => C)
      (Eventually.of_forall (fun n =>
        ((hfn n).mono (show uIoc (0:ℝ) t ⊆ Ici 0 by rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc))
      (Eventually.of_forall (fun n => ae_of_all _ fun s hs =>
        hb n s (by rw [uIoc_of_le ht] at hs; exact ⟨hs.1.le,hs.2⟩)))
      (intervalIntegrable_const)
      (ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le))
    simpa only [intervalIntegral.integral_zero] using H
  have hFTC (n : ℕ) : (∫ s in 0..t, fn n s) =
      (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ (radialCutoffLp hfinite o n)
    have hAint : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := ((cheegerHeat_continuousOn hfinite h A).mono
      (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfinite h hu ht)
    rw [← T.intervalIntegral_comp_comm hAint,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_radialCutoff_eq_inner hfinite o n] using H
  have hsp := (integral_radialCutoff_tendsto o
    (integrable_of_memLp_mul_exp (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1 hdecay)).sub
      (integral_radialCutoff_tendsto o (integrable_of_memLp_mul_exp hU hdecay))
  rw [show (fun n => ∫ s in 0..t, fn n s) = (fun n =>
    (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m)) from funext hFTC] at htime
  exact sub_eq_zero.mp (tendsto_nhds_unique hsp htime)
end WeakHessian

end
end InlinedFile0

end OAI
