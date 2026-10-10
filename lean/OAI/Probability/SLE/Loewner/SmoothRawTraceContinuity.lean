import OAI.Probability.SLE.Loewner.SmoothRawTrace
import OAI.Probability.SLE.Loewner.RawTipTimeContinuity

namespace OAI

/-! Radial approximations converge uniformly away from time zero.
Consequently the raw smooth-driver tip is continuous at positive times. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem smooth_trace_uniform_radial_limit (b : Driver) (b' : ℝ → ℝ)
    {L : ℝ≥0} (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L)
    (a R : ℝ≥0) (ha : 0 < a) (hsmall : (L : ℝ)^2*(a : ℝ) ≤ 1) :
    TendstoUniformlyOn
      (fun n : ℕ => fun T : ℝ≥0 => inverseFlow 1 b T
        ((b T : ℂ)+((1/((n : ℝ)+1) : ℝ) : ℂ)*I))
      (fun T : ℝ≥0 => trace 1 b T) atTop (Icc a R) := by
  let C : ℝ := Real.exp ((4*(Real.sqrt a)⁻¹^2)*((R : ℝ)-a))
  have hzero : Tendsto (fun n : ℕ => (1/((n : ℝ)+1))*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hzero.eventually (Iio_mem_nhds hε)] with n hn T hT
  have hy : 0 < 1/((n : ℝ)+1) := by positivity
  have hdt (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :=
    (hd t ht.1).mono (show Icc 0 (T : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
  have h := inverseFlow_smooth_trace_error b T b' hdt L.coe_nonneg
    (show 0 < (a : ℝ) from ha) (show (a : ℝ) ≤ T from hT.1)
    (fun t ht => hb t ht.1) hsmall hy
  have hbound : dist (inverseFlow 1 b T
      ((b T : ℂ)+((1/((n : ℝ)+1) : ℝ) : ℂ)*I)) (trace 1 b T) ≤
      (1/((n : ℝ)+1))*C := by
    apply h.trans
    dsimp [C]
    gcongr
    exact hT.2
  simpa only [dist_comm] using hbound.trans_lt hn

theorem continuousOn_smooth_trace_Icc (b : Driver) (b' : ℝ → ℝ)
    {L : ℝ≥0} (hLip : LipschitzWith L (driverValue b))
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L)
    (a R : ℝ≥0) (ha : 0 < a) (hsmall : (L : ℝ)^2*(a : ℝ) ≤ 1) :
    ContinuousOn (fun T : ℝ≥0 => trace 1 b T) (Icc a R) := by
  exact (smooth_trace_uniform_radial_limit b b' hd hb a R ha hsmall).continuousOn
    (Eventually.frequently (Eventually.of_forall (fun n => (continuous_raw_radial_time b hLip
      (show 0 < 1/((n : ℝ)+1) by positivity)).continuousOn)))

end SLEExactGauge.Target

end

end OAI
