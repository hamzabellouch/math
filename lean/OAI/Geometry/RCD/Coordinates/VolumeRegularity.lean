import OAI.Geometry.RCD.Metric.VolumeDerivative

namespace OAI

/-! # Absolute continuity of radial ball volumes from CD alone -/

open Set Metric MeasureTheory

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.ball_volume_absolutelyContinuous {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    AbsolutelyContinuousOnInterval (fun r => (hausdorff n X).real (ball p r)) u v := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  by_cases hK : 0 ≤ K
  · exact RegularPointCoordinates.ball_volume_absolutelyContinuous (n - 1) (by norm_num)
      (hX.zero_model_ballVolumeComparison hn hK) p hu huv
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hKneg : K < 0 := lt_of_not_ge hK
  let a := Real.sqrt (-K / ((n : ℝ) - 1))
  let model : ℝ → ℝ := fun r => r * Real.sinh (r * a) ^ (n - 1)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) (sub_pos.mpr hn1))
  have hmodel : ContDiff ℝ 1 model := by dsimp only [model]; fun_prop
  obtain ⟨L, hL⟩ := hmodel.contDiffOn.exists_lipschitzOnWith
    (s := Icc u v) (by decide) (convex_Icc u v) isCompact_Icc
  have hm0 : 0 < model u := mul_pos hu (pow_pos (Real.sinh_pos_iff.mpr (mul_pos hu ha)) _)
  have hVmono : MonotoneOn (fun r => (hausdorff n X).real (ball p r)) (Icc u v) := by
    intro r hr s hs hrs
    exact measureReal_mono (ball_subset_ball hrs) (hX.finiteOnBounded _ isBounded_ball).ne
  have hVupper (r : ℝ) (hr : r ∈ Icc u v) :
      (hausdorff n X).real (ball p r) ≤ (hausdorff n X).real (ball p v) :=
    measureReal_mono (ball_subset_ball hr.2) (hX.finiteOnBounded _ isBounded_ball).ne
  have hmlower (r : ℝ) (hr : r ∈ Icc u v) : model u ≤ model r := by
    have hs : 0 < Real.sinh (u * a) := Real.sinh_pos_iff.mpr (mul_pos hu ha)
    have hmon := Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hr.1 ha.le)
    exact mul_le_mul hr.1 (pow_le_pow_left₀ hs.le hmon _)
      (pow_nonneg hs.le _) (hu.le.trans hr.1)
  have hBG := hX.cd.hyperbolic_radial_ballVolumeComparison (hausdorff n X)
    hX.fullSupport hX.finiteOnBounded hn hKneg
  have hcross (r : ℝ) (hr : r ∈ Icc u v) (s : ℝ) (_hs : s ∈ Icc u v) (hrs : r ≤ s) :
      (hausdorff n X).real (ball p s) * model r ≤
        (hausdorff n X).real (ball p r) * model s := hBG p r s (hu.trans_le hr.1) hrs
  have hLip := volume_profile_lipschitzOn hm0 measureReal_nonneg L hVmono
    (fun _ _ => measureReal_nonneg) hVupper hmlower hL hcross
  rw [← uIcc_of_le huv] at hLip
  exact hLip.absolutelyContinuousOnInterval

end RegularPointCoordinates

end OAI
