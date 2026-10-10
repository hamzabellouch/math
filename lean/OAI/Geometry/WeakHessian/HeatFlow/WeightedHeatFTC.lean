import Mathlib
import OAI.Geometry.WeakHessian.Measure.RadialCutoffLp
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile43
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_weighted_FTC {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, ∫ x,cheegerHeat h s A x*φ x ∂m) =
      (∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
  let fn (n : ℕ) (s : ℝ) := ∫ x,cheegerHeat h s A x*φ x*radialCutoff o n x ∂m
  have he (n : ℕ) (s : ℝ) : fn n s = ⟪(hcut n).toLp _,cheegerHeat h s A⟫_ℝ := by
    simp only [fn,mul_assoc,integral_mul_eq_inner_toLp _ (hcut n)]
  have hc (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    change ContinuousOn (fun s => fn n s) (Ici 0)
    simp_rw [he]
    exact (innerSL ℝ ((hcut n).toLp _)).continuous.comp_continuousOn (cheegerHeat_continuousOn hfin h A)
  have hn (n : ℕ) : MemLp (fun x => (φ x*radialCutoff o n x)*Real.exp (-V x)) 2 m := by
    convert radial_mul_memLp hφ o n using 1
    funext x; ring
  have hnn (n : ℕ) : ‖(hn n).toLp _‖ ≤ ‖hφ.toLp _‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hn n).coeFn_toLp,hφ.coeFn_toLp] with x hx hy
    rw [hx,hy]
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg (φ x)) (radialCutoff_le_one o n x)) (abs_nonneg _)
  let M := ‖hA.toLp (fun x => A x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 t) : ‖fn n s‖ ≤ M*‖hφ.toLp _‖ := by
    have H := weighted_pairing (hcd.cheegerHeat_weighted hfin o h A hV hA hs.1).1 (hn n)
    simp only [← mul_assoc] at H
    exact H.2.trans (mul_le_mul
      ((hcd.cheegerHeat_weighted_norm hfin o h A hV hA hs.1).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))) (norm_nonneg _)))
      (hnn n) (norm_nonneg _) (by dsimp [M]; positivity))
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop
      (𝓝 (∫ x,cheegerHeat h s A x*φ x ∂m)) :=
    integral_radialCutoff_tendsto o (weighted_pairing (hcd.cheegerHeat_weighted hfin o h A hV hA hs).1 hφ).1
  have htime : Tendsto (fun n => ∫ s in 0..t,fn n s) atTop
      (𝓝 (∫ s in 0..t,∫ x,cheegerHeat h s A x*φ x ∂m)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M*‖hφ.toLp _‖)
    · exact Eventually.of_forall fun n => ((hc n).mono (show uIoc (0:ℝ) t ⊆ Ici 0 by
        rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun n => ae_of_all _ fun s hs => hb n s (by
        rw [uIoc_of_le ht] at hs; exact ⟨hs.1.le,hs.2⟩)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le)
  have hFTC (n : ℕ) : (∫ s in 0..t,fn n s) =
      (∫ x,cheegerHeat h t u x*φ x*radialCutoff o n x ∂m)-(∫ x,u x*φ x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ ((hcut n).toLp _)
    have hai : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t :=
      ((cheegerHeat_continuousOn hfin h A).mono (show uIcc (0:ℝ) t ⊆ Ici 0 by
        rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfin h hu ht)
    rw [← T.intervalIntegral_comp_comm hai,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_mul_eq_inner_toLp _ (hcut n),← mul_assoc,fn] using H
  have hs := (integral_radialCutoff_tendsto o
    (weighted_pairing (hcd.cheegerHeat_weighted hfin o h u hV hU ht).1 hφ).1).sub
    (integral_radialCutoff_tendsto o (weighted_pairing hU hφ).1)
  simp_rw [hFTC] at htime
  exact tendsto_nhds_unique htime hs

lemma CurvatureDimension.cheegerHeat_weighted_deriv {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x,cheegerHeat h s u x*φ x ∂m)
      (∫ x,cheegerHeat h t A x*φ x ∂m) t := by
  let g (s : ℝ) := ∫ x,cheegerHeat h (max s 0) A x*φ x ∂m
  have hc : Continuous g := hcd.cheegerHeat_weighted_pairing_continuous hfin o h A hV hA hφ hcut
  have he (r : ℝ) (hr : 0 ≤ r) : (∫ s in 0..r,g s) =
      (∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
    rw [← hcd.cheegerHeat_weighted_FTC hfin o h hu hV hU hA hφ hcut hr]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr] at hs
    simp only [g,max_eq_left hs.1]
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).add_const (∫ x,u x*φ x ∂m)
  have H : HasDerivAt (fun r => (∫ s in 0..r,g s)+(∫ x,u x*φ x ∂m))
      (∫ x,cheegerHeat h t A x*φ x ∂m) t := by
    simpa only [g,max_eq_left ht.le] using hd
  apply H.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  rw [he r hr.le]
  ring
end WeakHessian

end
end InlinedFile43

end OAI
