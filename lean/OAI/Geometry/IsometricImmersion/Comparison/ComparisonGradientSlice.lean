import OAI.Geometry.IsometricImmersion.Estimates.MovingSourceBounds
import OAI.Geometry.IsometricImmersion.Energy.MovingEnergyGradient

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem fixed_slice_gradient_le_moving_energy
    {S v : Coord → ℝ} {V : Set Coord} {xl xr a speed t pulseRadius s0 : ℝ}
    (hV : IsOpen V) (hS : ContinuousOn S V) (hv : ContDiffOn ℝ ∞ v V)
    (hs0 : 0 < s0) (hpulse : 0 ≤ pulseRadius)
    (hleft : inwardLeft xl a speed t ≤ -pulseRadius)
    (hright : pulseRadius ≤ inwardRight xr a speed t)
    (hmem : ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
      coordinatePoint x t ∈ V)
    (hfloor : ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
      s0 ≤ S (coordinatePoint x t)) (i : Fin 2) :
    Real.sqrt (∫ x in Icc (-pulseRadius) pulseRadius, (coordPartial i v (boxPoint x t))^2) ≤
      Real.sqrt (2*(1+1/s0))*Real.sqrt (movingEnergy xl xr a speed S v t) := by
  let l := inwardLeft xl a speed t
  let r := inwardRight xr a speed t
  let K := 2*(1+1/s0)
  have hlr : l ≤ r := hleft.trans ((by linarith : -pulseRadius ≤ pulseRadius).trans hright)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpointContinuous : Continuous (fun x : ℝ => coordinatePoint x t) := by
    unfold coordinatePoint
    fun_prop
  have hvi : ContinuousOn (fun x => coordPartial i v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV i).continuousOn.comp hpointContinuous.continuousOn hmem
  have hvt : ContinuousOn (fun x => coordPartial 1 v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV 1).continuousOn.comp hpointContinuous.continuousOn hmem
  have hvx : ContinuousOn (fun x => coordPartial 0 v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV 0).continuousOn.comp hpointContinuous.continuousOn hmem
  have hSc : ContinuousOn (fun x => S (coordinatePoint x t)) (Icc l r) :=
    hS.comp hpointContinuous.continuousOn hmem
  have he : ContinuousOn (fun x => energyDensity S v (coordinatePoint x t)) (Icc l r) :=
    ((hvt.pow 2).add (hSc.mul (hvx.pow 2))).div_const 2
  have hsmall : (∫ x in -pulseRadius..pulseRadius, (coordPartial i v (coordinatePoint x t))^2) ≤
      ∫ x in l..r, (coordPartial i v (coordinatePoint x t))^2 :=
    intervalIntegral.integral_mono_interval hleft (by linarith) hright
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      ((hvi.pow 2).intervalIntegrable_of_Icc hlr)
  have henergy : (∫ x in l..r, (coordPartial i v (coordinatePoint x t))^2) ≤
      K*movingEnergy xl xr a speed S v t := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hlr
      ((hvi.pow 2).intervalIntegrable_of_Icc hlr)
      ((continuousOn_const.mul he).intervalIntegrable_of_Icc hlr) (fun x hx => by
        have hscalar := scalar_gradient_le_energy hs0 (hfloor x hx)
          (a := coordPartial 1 v (coordinatePoint x t)) (b := coordPartial 0 v (coordinatePoint x t))
        have hi : (coordPartial i v (coordinatePoint x t))^2 ≤
            (coordPartial 1 v (coordinatePoint x t))^2+(coordPartial 0 v (coordinatePoint x t))^2 := by
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith [sq_nonneg (coordPartial 0 v (coordinatePoint x t)),
            sq_nonneg (coordPartial 1 v (coordinatePoint x t))]
        exact hi.trans hscalar)
    dsimp only [Pi.pow_apply,Pi.mul_apply] at hmono
    simpa only [intervalIntegral.integral_const_mul,movingEnergy,movingIntervalIntegral,l,r,K] using hmono
  have hroot := Real.sqrt_le_sqrt (hsmall.trans henergy)
  rw [Real.sqrt_mul hK] at hroot
  have hpoint : (fun x => coordPartial i v (coordinatePoint x t)^2) =
      (fun x => coordPartial i v (boxPoint x t)^2) := by
    funext x
    have he : coordinatePoint x t=boxPoint x t := by ext j; fin_cases j <;> simp [coordinatePoint,boxPoint]
    rw [he]
  simpa only [intervalIntegral.integral_of_le (by linarith : -pulseRadius ≤ pulseRadius),
    ← integral_Icc_eq_integral_Ioc,hpoint,K] using hroot

end SmoothLocal.Hyperbolic

end

end OAI
