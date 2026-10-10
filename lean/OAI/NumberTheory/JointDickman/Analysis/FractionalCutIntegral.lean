import OAI.NumberTheory.JointDickman.Analysis.FractionalPowerHorizontal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # Dominated convergence on the integrable side of the fractional cut -/
namespace JointDickman
open Filter Set MeasureTheory
open scoped Topology

theorem fractionalCut_upper_integral {z η R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hη : 0 < η) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioc 0 η,
      F (-(t:ℂ)+(ε:ℂ)*Complex.I)*fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioc 0 η,
        F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I)))) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hF
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hpath (ε : ℝ) : Continuous (fun t : ℝ => -(t:ℂ)+(ε:ℂ)*Complex.I) := by fun_prop
  have hmap (ε : ℝ) (hε : 0 < ε) (hεη : ε < η) (t : ℝ) (ht : t ∈ Ioc 0 η) :
      -(t:ℂ)+(ε:ℂ)*Complex.I ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    calc
      _ ≤ ‖-(t:ℂ)‖+‖(ε:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = t+ε := by simp [abs_of_pos ht.1,abs_of_pos hε]
      _ ≤ R := by linarith [ht.2]
  have hpow : IntegrableOn (fun t : ℝ => t^(-z)) (Ioc 0 η) := by
    apply ((integrable_abs_rpow_on_bounded_interval (a := 0) (b := η) hz1).mono_set
      Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp only
    rw [abs_of_pos ht.1]
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => B*t^(-z))
  · filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    have hFε : ContinuousOn (fun t : ℝ => F (-(t:ℂ)+(ε:ℂ)*Complex.I)) (Ioc 0 η) :=
      hF.comp' (hpath ε).continuousOn (hmap ε hε.1 hε.2)
    have hKε : ContinuousOn (fun t : ℝ => fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I))
        (Ioc 0 η) := by
      intro t _
      have hslit : -(t:ℂ)+(ε:ℂ)*Complex.I ∈ Complex.slitPlane := by
        right
        simpa using hε.1.ne'
      have hk : ContinuousAt (fractionalPowerKernel z) (-(t:ℂ)+(ε:ℂ)*Complex.I) := by
        change ContinuousAt (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) _
        exact (continuousAt_const.mul (continuousAt_clog hslit)).cexp
      exact (ContinuousAt.comp (f := fun t : ℝ => -(t:ℂ)+(ε:ℂ)*Complex.I)
        hk (hpath ε).continuousAt).continuousWithinAt
    exact (hFε.mul hKε).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul]
    apply mul_le_mul (le_trans (hC _ (hmap ε hε.1 hε.2 t ht)) (le_max_left _ _))
      _ (norm_nonneg _) hB
    simpa only [Complex.ofReal_neg,abs_neg,abs_of_pos ht.1] using
      (fractionalPower_horizontal_bound hz (u := -t) (v := ε) (neg_ne_zero.mpr ht.1.ne'))
  · exact hpow.const_mul B
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htR : -(t:ℂ) ∈ Metric.ball 0 R := by
      simp only [Metric.mem_ball,dist_zero_right,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ht.1]
      linarith [ht.2]
    have hc := hF.continuousAt (Metric.closedBall_mem_nhds_of_mem htR)
    have he : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hp : Tendsto (fun ε : ℝ => -(t:ℂ)+(ε:ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (-(t:ℂ))) := by
      simpa only [zero_mul,add_zero] using he.mul_const Complex.I |>.const_add (-(t:ℂ))
    exact (hc.tendsto.comp hp).mul (fractionalPower_upper_horizontal z ht.1)

end JointDickman

end OAI
