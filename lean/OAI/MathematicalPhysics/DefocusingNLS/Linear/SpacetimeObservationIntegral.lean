import OAI.MathematicalPhysics.DefocusingNLS.Linear.SpacetimeBallObservation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Passage to the limit in the compact-observation energy integral -/

open Set MeasureTheory Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_spacetime_observation_integral (T R B c C : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (u : ℕ → C(Icc (0 : ℝ) T × E, ℂ)) (v : C(Icc (0 : ℝ) T × E, ℂ))
    (hu : ∀ n t y, ‖u n (t, y)‖ ≤ B) (hv : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..T, Real.exp (-c * (T - s)) *
      (C * ‖spacetimeBallPath T R (u n) (projIcc 0 T hT s)‖ ^ 2)) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, Real.exp (-c * (T - s)) *
        (C * ‖spacetimeBallPath T R v (projIcc 0 T hT s)‖ ^ 2))) := by
  let p := projIcc 0 T hT
  have hpath := (continuous_spacetimeBallPath T R).continuousAt.tendsto.comp hv
  have hs (s : ℝ) : Tendsto (fun n => spacetimeBallPath T R (u n) (p s)) atTop
      (𝓝 (spacetimeBallPath T R v (p s))) :=
    (continuous_eval_const (p s)).continuousAt.tendsto.comp hpath
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Icc 0 T))
    (fun _ => C * B ^ 2)
    (fun n => (show Continuous (fun s => Real.exp (-c * (T - s)) *
      (C * ‖spacetimeBallPath T R (u n) (p s)‖ ^ 2)) by
        exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (-c * (T - s)))).mul
          (continuous_const.mul (((spacetimeBallPath T R (u n)).continuous.comp
            continuous_projIcc).norm.pow 2))).aestronglyMeasurable)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hb := spacetimeBallPath_norm_le T R B hB (u n) (hu n) (p s)
      have he : Real.exp (-c * (T - s)) ≤ 1 := Real.exp_le_one_iff.mpr
        (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hs.2)])
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc
        _ ≤ 1 * (C * ‖spacetimeBallPath T R (u n) (p s)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right he (by positivity)
        _ ≤ C * B ^ 2 := by simpa only [one_mul] using
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) hC)
    (ae_of_all _ (fun s => tendsto_const_nhds.mul (tendsto_const_nhds.mul ((hs s).norm.pow 2))))
  simpa only [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc, p] using h

end DefocusingNLS

end OAI
