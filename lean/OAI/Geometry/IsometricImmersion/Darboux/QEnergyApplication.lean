import OAI.Geometry.IsometricImmersion.Darboux.QResidualL2
import OAI.Geometry.IsometricImmersion.Energy.MovingSlabEnergy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qHighBTheta_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (qHighBTheta g z ell) U :=
  (heightQCoefficient_contDiffOn hg hU hz hxx 3).add (contDiffOn_const.mul
    (partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx 4) hU 0))

theorem qHighBXi_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (qHighBXi g z ell) U :=
  (heightQCoefficient_contDiffOn hg hU hz hxx 2).add (contDiffOn_const.mul
    (partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx 5) hU 0))

theorem actualQHighRemainder_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ) :
    ContDiffOn ℝ ∞ (actualQHighRemainder g z m) U := by
  have hu := horizontalJet_contDiffOn hU hz (m + 3)
  have hx := partial_contDiffOn hu hU 0
  have ht := partial_contDiffOn hu hU 1
  have hP := heightQCoefficient_contDiffOn hg hU hz hxx 4
  have hS := heightQCoefficient_contDiffOn hg hU hz hxx 5
  have hbt := qHighBTheta_contDiffOn hg hU hz hxx (m + 3)
  have hbx := qHighBXi_contDiffOn hg hU hz hxx (m + 3)
  have hf := ((((partial_contDiffOn ht hU 1).sub
    (hP.mul (partial_contDiffOn ht hU 0))).sub
      (hS.mul (partial_contDiffOn hx hU 0))).sub (hbt.mul ht)).sub (hbx.mul hx)
  apply hf.congr
  intro p hp
  have he := actual_Q_hyperbolic_equation hg hU hz hD hxx m hp
  change actualQHighRemainder g z m p =
    coordPartial 1 (coordPartial 1 (horizontalJet z (m + 3))) p -
      heightQCoefficient g z 4 p * coordPartial 0 (coordPartial 1 (horizontalJet z (m + 3))) p -
      heightQCoefficient g z 5 p * coordPartial 0 (coordPartial 0 (horizontalJet z (m + 3))) p -
      qHighBTheta g z (m + 3) p * coordPartial 1 (horizontalJet z (m + 3)) p -
      qHighBXi g z (m + 3) p * coordPartial 0 (horizontalJet z (m + 3)) p
  unfold hyperbolicOperator at he
  linarith

theorem spatialProductL2Budget_mono_width
    {lengthFloor left right width : ℝ} (H : ℝ≥0) (n : ℕ)
    (hwidth : right - left ≤ width) :
    spatialProductL2Budget lengthFloor left right H n ≤
      spatialProductL2Budget lengthFloor 0 width H n := by
  have hvol : volume (Icc left right) ≤ volume (Icc (0 : ℝ) width) := by
    rw [Real.volume_Icc, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_le_ofReal hwidth
  exact mul_le_mul' le_rfl (add_le_add le_rfl
    (ENNReal.rpow_le_rpow hvol (by norm_num : 0 ≤ 1 / (2 : ℝ))))

theorem qRemainderSliceBudget_mono_width
    {C Cfirst lengthFloor left right width : ℝ} (H : ℝ≥0) (m : ℕ)
    (hwidth : right - left ≤ width) :
    qRemainderSliceBudget C Cfirst lengthFloor left right H m ≤
      qRemainderSliceBudget C Cfirst lengthFloor 0 width H m := by
  have hword (w : ChainWord) : qWordSliceBudget C lengthFloor left right H w ≤
      qWordSliceBudget C lengthFloor 0 width H w := by
    apply Finset.sum_le_sum
    intro _ _
    exact mul_le_mul' le_rfl (spatialProductL2Budget_mono_width H w.arity hwidth)
  have hsum (ws : List ChainWord) : qChainSliceBudget C lengthFloor left right H ws ≤
      qChainSliceBudget C lengthFloor 0 width H ws := by
    induction ws with
    | nil => exact le_rfl
    | cons w ws ih => exact add_le_add (hword w) ih
  exact add_le_add (hsum (topResidualWords m)) le_rfl

theorem actualQ_source_norm_le
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor width C Cfirst : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hupper : right - left ≤ width) (hm : 8 ≤ m + 3) (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r x, x ∈ Icc left right →
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    Real.sqrt (∫ x in left..right, actualQHighRemainder g z m (coordinatePoint x theta) ^ 2) ≤
      (qRemainderSliceBudget C Cfirst lengthFloor 0 width H m).toReal := by
  have hlr : left ≤ right := by linarith
  have hmem := actualQHighRemainder_slice_memLp_two hg hU hz hxx m hseg
  have hnorm := (actualQHighRemainder_slice_eLpNorm_two hg hU hz hxx hseg hlength hwidth
    hm hC hCfirst hL2 hcoeff hfirst2 hfirst3).trans
      (qRemainderSliceBudget_mono_width H m hupper)
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    sqrt_integral_square_eq_L2_norm hmem, Lp.norm_def, eLpNorm_congr_ae hmem.coeFn_toLp]
  exact ENNReal.toReal_mono (qRemainderSliceBudget_lt_top C Cfirst lengthFloor 0 width H m).ne hnorm

theorem actual_Q_moving_slab_energy
    {g : MetricField} {z : Coord → ℝ} {radius lo hi xl xr a b speed s0 M : ℝ}
    (hg : SmoothPositiveOn g (coordinateRectangle radius lo hi))
    (hz : ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi))
    (hD : ∀ p ∈ coordinateRectangle radius lo hi,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0)
    (m : ℕ) (hradius : 0 < radius) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius) (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlength : 2 * speed * (b - a) < xr - xl) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p)
    (hcoeff : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |qHighBTheta g z (m + 3) p| ≤ M ∧ |qHighBXi g z (m + 3) p| ≤ M ∧
        |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M ∧
        |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M ∧
        |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M)
    (hchar : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) :
    Real.sqrt (movingEnergy xl xr a speed (heightQCoefficient g z 5) (horizontalJet z (m + 3)) b) ≤
      Real.exp ((8 * M * (1 + 1 / s0)) * (b - a)) *
        (Real.sqrt (∫ xi in xl..xr, energyDensity (heightQCoefficient g z 5)
          (horizontalJet z (m + 3)) (coordinatePoint xi a)) +
            ∫ t in a..b, movingSourceNorm xl xr a speed (actualQHighRemainder g z m) t) := by
  have hU := coordinateRectangle_isOpen radius lo hi
  apply moving_slab_energy_propagation
    (heightQCoefficient_contDiffOn hg hU hz hxx 4)
    (heightQCoefficient_contDiffOn hg hU hz hxx 5)
    (qHighBTheta_contDiffOn hg hU hz hxx (m + 3))
    (qHighBXi_contDiffOn hg hU hz hxx (m + 3))
    (horizontalJet_contDiffOn hU hz (m + 3))
    (actualQHighRemainder_contDiffOn hg hU hz hD hxx m)
    hradius hab hspeed hxl hxr ha hb hlength hs0 hM hSfloor hcoeff hchar
  intro p hp
  exact actual_Q_hyperbolic_equation hg hU hz hD hxx m
    (shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength hp)

theorem actual_Q_moving_slab_energy_with_source_budget
    {g : MetricField} {z : Coord → ℝ}
    {radius lo hi xl xr a b speed s0 M lengthFloor C Cfirst : ℝ} {H : ℝ≥0}
    (hg : SmoothPositiveOn g (coordinateRectangle radius lo hi))
    (hz : ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi))
    (hD : ∀ p ∈ coordinateRectangle radius lo hi,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0)
    (m : ℕ) (hm : 8 ≤ m + 3)
    (hradius : 0 < radius) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius) (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlen : 0 < lengthFloor) (hwidth : lengthFloor ≤ xr - xl - 2 * speed * (b - a))
    (hs0 : 0 < s0) (hM : 0 ≤ M) (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst)
    (hSfloor : ∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p)
    (hcoeff : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |qHighBTheta g z (m + 3) p| ≤ M ∧ |qHighBXi g z (m + 3) p| ≤ M ∧
        |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M ∧
        |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M ∧
        |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M)
    (hchar : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed)
    (hL2 : ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
      (inwardLeft xl a speed t) (inwardRight xr a speed t) (m + 2) H)
    (houter : ∀ w ∈ topResidualWords m, ∀ r p, p ∈ shrinkingSlab xl xr a b speed →
      |qCoordinateChainCoefficient g z w r p| ≤ C)
    (hfirst2 : ∀ p ∈ shrinkingSlab xl xr a b speed, |coordPartial 0 (heightQCoefficient g z 2) p| ≤ Cfirst)
    (hfirst3 : ∀ p ∈ shrinkingSlab xl xr a b speed, |coordPartial 0 (heightQCoefficient g z 3) p| ≤ Cfirst) :
    Real.sqrt (movingEnergy xl xr a speed (heightQCoefficient g z 5) (horizontalJet z (m + 3)) b) ≤
      Real.exp ((8 * M * (1 + 1 / s0)) * (b - a)) *
        (Real.sqrt (∫ xi in xl..xr, energyDensity (heightQCoefficient g z 5)
          (horizontalJet z (m + 3)) (coordinatePoint xi a)) +
            (b - a) * (qRemainderSliceBudget C Cfirst lengthFloor 0 (xr - xl) H m).toReal) := by
  have hlength : 2 * speed * (b - a) < xr - xl := by linarith
  have hU := coordinateRectangle_isOpen radius lo hi
  have hsub := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hprop := actual_Q_moving_slab_energy hg hz hD hxx m hradius hab hspeed
    hxl hxr ha hb hlength hs0 hM hSfloor hcoeff hchar
  have hforce (t : ℝ) (ht : t ∈ Icc a b) :
      movingSourceNorm xl xr a speed (actualQHighRemainder g z m) t ≤
        (qRemainderSliceBudget C Cfirst lengthFloor 0 (xr - xl) H m).toReal := by
    have hwlow : lengthFloor ≤ inwardRight xr a speed t - inwardLeft xl a speed t := by
      unfold inwardRight inwardLeft
      have hmul := mul_le_mul_of_nonneg_left ht.2 hspeed
      nlinarith
    have hwup : inwardRight xr a speed t - inwardLeft xl a speed t ≤ xr - xl := by
      unfold inwardRight inwardLeft
      have hmul : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
      linarith
    exact actualQ_source_norm_le hg hU hz hxx
      (fun x hx => hsub (point_mem_shrinkingSlab ht hx)) hlen hwlow hwup hm hC hCfirst
      (hL2 t ht) (fun w hw r x hx => houter w hw r _ (point_mem_shrinkingSlab ht hx))
      (fun x hx => hfirst2 _ (point_mem_shrinkingSlab ht hx))
      (fun x hx => hfirst3 _ (point_mem_shrinkingSlab ht hx))
  have hR := actualQHighRemainder_contDiffOn hg hU hz hD hxx m
  have hgeo (t : ℝ) (ht : t ∈ Icc a b) := inward_interval_geometry hab hspeed hxl hxr hlength ht
  have hfc := movingSourceNorm_continuousOn hR hradius
    (fun t ht => (hgeo t ht).1) (fun t ht => (hgeo t ht).2.1)
    (fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩)
  have hfI : IntervalIntegrable
      (movingSourceNorm xl xr a speed (actualQHighRemainder g z m)) volume a b :=
    hfc.intervalIntegrable_of_Icc hab
  have hInt : (∫ t in a..b, movingSourceNorm xl xr a speed (actualQHighRemainder g z m) t) ≤
      (b - a) * (qRemainderSliceBudget C Cfirst lengthFloor 0 (xr - xl) H m).toReal := by
    have hi := intervalIntegral.integral_mono_on hab hfI intervalIntegrable_const hforce
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
  exact hprop.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hInt) (Real.exp_pos _).le)

end SmoothLocal.HighEquation

end

end OAI
