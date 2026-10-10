import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakObservation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Integrated compact observation for the actual linearized evolution

Bounded weakly null data have vanishing local observation integrated over
any fixed time interval. This is the compact term used in the time-one
energy argument; no spectral-decay assumption occurs here.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

theorem tendsto_homogeneousLinearized_timeObservation (a b k T R M c : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (q : HomogeneousY a k)
    (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..T, Real.exp (-c * (T - s)) *
      ‖homogeneousLocalL2Observation a k R ha ha1 hk
        (homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q (u n)
          (projIcc 0 T hT s))‖ ^ 2) atTop (𝓝 0) := by
  let U := homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q
  let J := homogeneousLocalL2Observation a k R ha ha1 hk
  let C := ‖J‖ * ‖U‖ * M
  let F := fun n s => Real.exp (-c * (T - s)) * ‖J (U (u n) (projIcc 0 T hT s))‖ ^ 2
  have hcont (n : ℕ) : Continuous (F n) := by
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).mul
      ((J.continuous.comp ((U (u n)).continuous.comp continuous_projIcc)).norm.pow 2)
  have hbound (n : ℕ) (s : ℝ) : ‖F n s‖ ≤ Real.exp (-c * (T - s)) * C ^ 2 := by
    have hv : ‖J (U (u n) (projIcc 0 T hT s))‖ ≤ C := calc
      _ ≤ ‖J‖ * ‖U (u n) (projIcc 0 T hT s)‖ := J.le_opNorm _
      _ ≤ ‖J‖ * ‖U (u n)‖ := mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm _ _) (norm_nonneg J)
      _ ≤ ‖J‖ * (‖U‖ * ‖u n‖) := mul_le_mul_of_nonneg_left (U.le_opNorm _) (norm_nonneg J)
      _ ≤ ‖J‖ * (‖U‖ * M) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg U)) (norm_nonneg J)
      _ = C := by dsimp only [C]; ring
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (Real.exp_pos _).le
  have hpoint (s : ℝ) : Tendsto (fun n => F n s) atTop (𝓝 0) := by
    have h := tendsto_homogeneousLinearized_localL2_of_weakNull a b k T R M ha ha1 hk hT
      m q (projIcc 0 T hT s) u hu hweak
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (h.norm.pow 2).const_mul (Real.exp (-c * (T - s)))
  have hdom : IntegrableOn (fun s => Real.exp (-c * (T - s)) * C ^ 2) (Ioc (0 : ℝ) T) :=
    (((Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).mul continuous_const).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) T)) (fun s => Real.exp (-c * (T - s)) * C ^ 2)
    (fun n => (hcont n).aestronglyMeasurable)
    hdom (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hpoint)
  simpa only [intervalIntegral.integral_of_le hT, integral_zero] using hlim

end DefocusingNLS

end OAI
