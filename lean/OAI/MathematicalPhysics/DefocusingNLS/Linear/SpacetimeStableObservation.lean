import OAI.MathematicalPhysics.DefocusingNLS.Linear.SpacetimeBallObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMap
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ObservationDecay

namespace OAI

/-! # Whole-space decay bounds the compact observation independently of the slab -/

open Set MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem spacetimeBallPath_norm_le_homogeneous (a k T R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : C(Icc (0 : ℝ) T × E, ℂ)) (w : Icc (0 : ℝ) T → HomogeneousY a k)
    (hw : ∀ t y, v (t, y) = homogeneousPhysicalCLM a k ha ha1 hk (w t) y)
    (t : Icc (0 : ℝ) T) :
    ‖spacetimeBallPath T R v t‖ ≤ ‖homogeneousPhysicalCLM a k ha ha1 hk‖ * ‖w t‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro y
  rw [spacetimeBallPath_apply, hw]
  exact (BoundedContinuousFunction.norm_coe_le_norm _ _).trans
    ((homogeneousPhysicalCLM a k ha ha1 hk).le_opNorm _)

theorem spacetime_stable_observation_integral_le (a k T R C A η : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (hC : 0 ≤ C) (_hA : 0 ≤ A) (c : ℝ)
    (v : C(Icc (0 : ℝ) T × E, ℂ)) (w : Icc (0 : ℝ) T → HomogeneousY a k)
    (hw : ∀ t y, v (t, y) = homogeneousPhysicalCLM a k ha ha1 hk (w t) y)
    (hdecay : ∀ t, ‖w t‖ ≤ A * Real.exp (-η * (t : ℝ))) :
    (∫ s in (0 : ℝ)..T, Real.exp (-c * (T - s)) *
      (C * ‖spacetimeBallPath T R v (projIcc 0 T hT s)‖ ^ 2)) ≤
      (C * (‖homogeneousPhysicalCLM a k ha ha1 hk‖ * A) ^ 2) *
        observationDecayIntegral c (2 * η) T := by
  let B : ℝ := ‖homogeneousPhysicalCLM a k ha ha1 hk‖ * A
  have heq (s : ℝ) : (B * Real.exp (-η * s)) ^ 2 =
      B ^ 2 * Real.exp (-(2 * η) * s) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hi : IntervalIntegrable (fun s : ℝ => Real.exp (-c * (T - s)) *
      (C * ‖spacetimeBallPath T R v (projIcc 0 T hT s)‖ ^ 2)) volume 0 T :=
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-c * (T - s)))).mul
      (continuous_const.mul (((spacetimeBallPath T R v).continuous.comp
        continuous_projIcc).norm.pow 2))).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun s : ℝ =>
      (C * B ^ 2) * (Real.exp (-c * (T - s)) * Real.exp (-(2 * η) * s))) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ =>
      (C * B ^ 2) * (Real.exp (-c * (T - s)) * Real.exp (-(2 * η) * s)))).intervalIntegrable _ _
  have hb (s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖spacetimeBallPath T R v (projIcc 0 T hT s)‖ ≤ B * Real.exp (-η * s) := by
    have hp : (projIcc 0 T hT s : ℝ) = s := congrArg Subtype.val (projIcc_of_mem hT hs)
    calc
      _ ≤ ‖homogeneousPhysicalCLM a k ha ha1 hk‖ * ‖w (projIcc 0 T hT s)‖ :=
        spacetimeBallPath_norm_le_homogeneous a k T R ha ha1 hk v w hw _
      _ ≤ ‖homogeneousPhysicalCLM a k ha ha1 hk‖ * (A * Real.exp (-η * s)) := by
        simpa only [hp] using mul_le_mul_of_nonneg_left (hdecay (projIcc 0 T hT s))
          (norm_nonneg (homogeneousPhysicalCLM a k ha ha1 hk))
      _ = _ := (mul_assoc _ _ _).symm
  have h := intervalIntegral.integral_mono_on hT hi hj (fun s hs => by
    calc
      _ ≤ Real.exp (-c * (T - s)) * (C * (B * Real.exp (-η * s)) ^ 2) := by
        gcongr
        exact hb s hs
      _ = _ := by rw [heq]; ring)
  simpa only [intervalIntegral.integral_const_mul, observationDecayIntegral, B] using h

end DefocusingNLS

end OAI
