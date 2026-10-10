import OAI.NumberTheory.JointDickman.Analysis.FractionalCutIntegral

namespace OAI

/-! # The common boundary value to the right of the branch point -/
namespace JointDickman
open Filter Set MeasureTheory
open scoped Topology

theorem fractionalPositive_integral {z c R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hc : 0 < c) (hR : 2*c < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioc 0 c,
      F ((t:ℂ)+(ε:ℂ)*Complex.I)*fractionalPowerKernel z ((t:ℂ)+(ε:ℂ)*Complex.I))
      (𝓝 0) (𝓝 (∫ t : ℝ in Ioc 0 c, F (t:ℂ)*(t^(-z):ℝ))) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hF
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hpath (ε : ℝ) : Continuous (fun t : ℝ => (t:ℂ)+(ε:ℂ)*Complex.I) := by fun_prop
  have hmap (ε : ℝ) (hε : |ε| < c) (t : ℝ) (ht : t ∈ Ioc 0 c) :
      (t:ℂ)+(ε:ℂ)*Complex.I ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    calc
      _ ≤ ‖(t:ℂ)‖+‖(ε:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = t+|ε| := by simp [abs_of_pos ht.1]
      _ ≤ R := by linarith [ht.2]
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, |ε| < c := by
    filter_upwards [Ioo_mem_nhds (by linarith : -c < 0) hc] with ε hε
    exact abs_lt.mpr hε
  have hpow : IntegrableOn (fun t : ℝ => t^(-z)) (Ioc 0 c) := by
    apply ((integrable_abs_rpow_on_bounded_interval (a := 0) (b := c) hz1).mono_set
      Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp only
    rw [abs_of_pos ht.1]
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => B*t^(-z))
  · filter_upwards [hsmall] with ε hε
    have hFε : ContinuousOn (fun t : ℝ => F ((t:ℂ)+(ε:ℂ)*Complex.I)) (Ioc 0 c) :=
      hF.comp' (hpath ε).continuousOn (hmap ε hε)
    have hKε : ContinuousOn (fun t : ℝ => fractionalPowerKernel z ((t:ℂ)+(ε:ℂ)*Complex.I))
        (Ioc 0 c) := by
      intro t ht
      have hslit : (t:ℂ)+(ε:ℂ)*Complex.I ∈ Complex.slitPlane := by
        left
        simpa using ht.1
      have hk : ContinuousAt (fractionalPowerKernel z) ((t:ℂ)+(ε:ℂ)*Complex.I) := by
        change ContinuousAt (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) _
        exact (continuousAt_const.mul (continuousAt_clog hslit)).cexp
      exact (ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)+(ε:ℂ)*Complex.I)
        hk (hpath ε).continuousAt).continuousWithinAt
    exact (hFε.mul hKε).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hsmall] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul]
    apply mul_le_mul (le_trans (hC _ (hmap ε hε t ht)) (le_max_left _ _))
      _ (norm_nonneg _) hB
    simpa only [abs_of_pos ht.1] using fractionalPower_horizontal_bound hz (v := ε) ht.1.ne'
  · exact hpow.const_mul B
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htR : (t:ℂ) ∈ Metric.ball 0 R := by
      simp only [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
      linarith [ht.2]
    have hp : Tendsto (fun ε : ℝ => (t:ℂ)+(ε:ℂ)*Complex.I) (𝓝 0) (𝓝 (t:ℂ)) := by
      simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
        ((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).const_add (t:ℂ)
    have hlim := ((hF.continuousAt (Metric.closedBall_mem_nhds_of_mem htR)).tendsto.comp hp).mul
      ((fractionalPower_continuousAt_positive z ht.1).tendsto.comp hp)
    rwa [fractionalPower_positive z ht.1] at hlim

end JointDickman

end OAI
