import OAI.Geometry.IsometricImmersion.Darboux.QSpatialSlabData

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_Q_spatial_induction_step
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (H A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ Hnew : ℝ≥0, H ≤ Hnew ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (m + 5) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ m + 4 → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      (∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (m + 2) H) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (m + 3) Hnew := by
  obtain ⟨B, hSource⟩ := exists_same_slice_actual_Q_source_norm_bound
    G R Z lengthFloor (xr - xl) H hG hR hlen hd hc m hm
  let I : ℝ≥0 := initialCutEnergyBudget (xr - xl) M A
  let C : ℝ := 8 * (M * (m + 4)) * (1 + 1 / s0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Ebound : ℝ≥0 := ⟨Real.exp (C * T) * ((I : ℝ) + T * (B : ℝ)), by positivity⟩
  let Hnew : ℝ≥0 := max H (spatialEnergyNormBudget s0 Ebound)
  refine ⟨Hnew, le_max_left _ _, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut hprev t ht
  let S := shrinkingSlab xl xr a b speed
  have hU := coordinateRectangle_isOpen radius lo hi
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU : S ⊆ coordinateRectangle radius lo hi :=
    shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have htime (v : ℝ) (hv : v ∈ Icc a b) : v ∈ Ioo lo hi :=
    ⟨ha.1.trans_le hv.1, hv.2.trans_lt hb.2⟩
  have hgeo (v : ℝ) (hv : v ∈ Icc a b) := inward_interval_geometry hab hspeed hxl hxr hlength hv
  have hsource (v : ℝ) (hv : v ∈ Icc a b) :
      movingSourceNorm xl xr a speed (actualQHighRemainder g z m) v ≤ (B : ℝ) := by
    have hwlow : lengthFloor ≤ inwardRight xr a speed v - inwardLeft xl a speed v := by
      unfold inwardRight inwardLeft
      have hvT : v - a ≤ T := (sub_le_sub_right hv.2 a).trans habT
      have hmul := mul_le_mul_of_nonneg_left hvT (by positivity : 0 ≤ 2 * speed)
      linarith
    have hwup : inwardRight xr a speed v - inwardLeft xl a speed v ≤ xr - xl := by
      unfold inwardRight inwardLeft
      have hh : 0 ≤ speed * (v - a) := mul_nonneg hspeed (sub_nonneg.mpr hv.1)
      linarith
    exact hSource g z (coordinateRectangle radius lo hi) S hg hU hz hSU hxx hcoords
      (fun p hp => coordinateMetricBound_to_horizontalTwoJet hgB hp)
      (hzB.mono (by norm_num) le_rfl) hdet hden v
      (inwardLeft xl a speed v) (inwardRight xr a speed v)
      (fun x hx => point_mem_shrinkingSlab hv hx) hwlow hwup (hprev v hv)
  have hS := heightQCoefficient_contDiffOn hg hU hz hxx 5
  have hInitial : Real.sqrt (∫ x in xl..xr,
      energyDensity (heightQCoefficient g z 5) (horizontalJet z (m + 3)) (coordinatePoint x a)) ≤ (I : ℝ) := by
    have hcutPoint (x : ℝ) (hx : x ∈ Icc xl xr) : coordinatePoint x a ∈ S := by
      apply point_mem_shrinkingSlab (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
      simpa only [inwardLeft, inwardRight, sub_self, mul_zero, add_zero, sub_zero] using hx
    apply initial_energy_bound_of_cut_jets hU hz hS
      (fun x hx => hSU (hcutPoint x hx))
      (by nlinarith [mul_nonneg hspeed (sub_nonneg.mpr hab)]) hM
      (fun x hx => (le_abs_self _).trans (hLow _ (hcutPoint x hx)).2.2.2.1) (m + 3) A
    simpa only [Nat.add_assoc] using hcut
  have hEt : Real.sqrt (movingEnergy xl xr a speed (heightQCoefficient g z 5)
      (horizontalJet z (m + 3)) t) ≤ (Ebound : ℝ) := by
    have httop : shrinkingSlab xl xr a t speed ⊆ S := shrinkingSlab_mono_top ht.2
    have hlenT : 2 * speed * (t - a) < xr - xl := by
      have hh := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ 2 * speed)
      nlinarith
    have hprop := actual_Q_moving_slab_energy hg hz hD hxx m hradius ht.1 hspeed
      hxl hxr ha (htime t ht) hlenT hs0 (by positivity : 0 ≤ M * (m + 4))
      (fun p hp => (hLow p (httop hp)).1)
      (fun p hp => by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc,
          show (3 : ℝ) + 1 = 4 by norm_num] using
        hLow.high_coefficients hM (m + 3) (httop hp))
      (fun p hp => (hLow p (httop hp)).2.2.2.2.2.2.2)
    have hR := actualQHighRemainder_contDiffOn hg hU hz hD hxx m
    have hforceCont : ContinuousOn (movingSourceNorm xl xr a speed (actualQHighRemainder g z m)) (Icc a t) :=
      movingSourceNorm_continuousOn hR hradius
        (fun v hv => (hgeo v ⟨hv.1, hv.2.trans ht.2⟩).1)
        (fun v hv => (hgeo v ⟨hv.1, hv.2.trans ht.2⟩).2.1)
        (fun v hv => htime v ⟨hv.1, hv.2.trans ht.2⟩)
    have hInt : (∫ v in a..t, movingSourceNorm xl xr a speed (actualQHighRemainder g z m) v) ≤
        (t - a) * (B : ℝ) := by
      have hh : (∫ v in a..t, movingSourceNorm xl xr a speed (actualQHighRemainder g z m) v) ≤
          ∫ v in a..t, (B : ℝ) := intervalIntegral.integral_mono_on ht.1
        (hforceCont.intervalIntegrable_of_Icc ht.1) intervalIntegrable_const
        (fun v hv => hsource v ⟨hv.1, hv.2.trans ht.2⟩)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
    have hduration : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hdurationT : t - a ≤ T := (sub_le_sub_right ht.2 a).trans habT
    have hfirst : Real.sqrt (movingEnergy xl xr a speed (heightQCoefficient g z 5)
        (horizontalJet z (m + 3)) t) ≤ Real.exp (C * (t - a)) * ((I : ℝ) + (t - a) * (B : ℝ)) :=
      hprop.trans (mul_le_mul_of_nonneg_left (add_le_add hInitial hInt) (Real.exp_pos _).le)
    exact hfirst.trans (mul_le_mul
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdurationT hC))
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hdurationT B.2))
      (by positivity) (Real.exp_pos _).le)
  intro i n hn
  by_cases hsmall : n ≤ m + 2
  · exact (hprev t ht i n hsmall).trans (by exact_mod_cast (le_max_left H (spatialEnergyNormBudget s0 Ebound)))
  · have he : n = m + 3 := by omega
    subst n
    have hn := spatialFirstJet_slice_eLpNorm_two_of_energy hU hz hS
      (fun x hx => hSU (point_mem_shrinkingSlab ht hx))
      (hgeo t ht).2.2.1.le hs0
      (fun x hx => (hLow _ (point_mem_shrinkingSlab ht hx)).1) (m + 3) Ebound hEt i
    exact hn.trans (by exact_mod_cast (le_max_right H (spatialEnergyNormBudget s0 Ebound)))

end SmoothLocal.HighEquation

end

end OAI
