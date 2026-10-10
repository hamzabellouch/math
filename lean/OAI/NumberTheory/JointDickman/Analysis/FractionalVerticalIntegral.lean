import OAI.NumberTheory.JointDickman.Analysis.FractionalContourRectangles
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Integrability and removal of the middle gaps on the vertical sides -/
namespace JointDickman
open Filter Set MeasureTheory Complex
open scoped Topology

theorem fractionalContour_vertical_integrable {z x a b : ℝ}
    (hz : 0 ≤ z) (hx : x ≠ 0) {F : ℂ → ℂ}
    (hF : ContinuousOn (fun t : ℝ => F ((x:ℂ)+(t:ℂ)*I)) (Icc a b)) :
    IntegrableOn (fun t : ℝ => fractionalContourIntegrand z F ((x:ℂ)+(t:ℂ)*I)) (Icc a b) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  have hK : Measurable (fun t : ℝ => fractionalPowerKernel z ((x:ℂ)+(t:ℂ)*I)) := by
    apply Complex.continuous_exp.measurable.comp
    apply measurable_const.mul
    apply Complex.measurable_log.comp
    fun_prop
  apply (integrableOn_const (C := max C 0 * |x|^(-z)) (s := Icc a b) (μ := volume) (by simp)).mono'
    ((hF.aestronglyMeasurable measurableSet_Icc).mul hK.aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change ‖F _ * fractionalPowerKernel z _‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul ((hC t ht).trans (le_max_left _ _))
    (fractionalPower_horizontal_bound hz hx) (norm_nonneg _) (le_max_right _ _)

theorem VIntegral_remove_middle_gap {f : ℂ → ℂ} {x T : ℝ} (hT : 0 < T)
    (hf : IntervalIntegrable (fun t : ℝ => f ((x:ℂ)+(t:ℂ)*I)) volume (-T) T) :
    Tendsto (fun ε : ℝ => VIntegral f x ε T + VIntegral f x (-T) (-ε))
      (𝓝[>] 0) (𝓝 (VIntegral f x (-T) T)) := by
  have h0 : (0:ℝ) ∈ uIcc (-T) T := by
    rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith,hT.le⟩
  have hnhds : uIcc (-T) T ∈ 𝓝 (0:ℝ) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_mem_nhds (by linarith) hT
  have hu : ContinuousAt (fun ε : ℝ => ∫ t in ε..T, f ((x:ℂ)+(t:ℂ)*I)) 0 :=
    (intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').mp hf)).continuousAt hnhds
  have hl : ContinuousAt (fun ε : ℝ => ∫ t in (-T)..ε, f ((x:ℂ)+(t:ℂ)*I)) 0 :=
    (intervalIntegral.continuousOn_primitive_interval ((intervalIntegrable_iff').mp hf)).continuousAt hnhds
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0:ℝ)
  have h := (hu.tendsto.const_smul I).add ((hl.tendsto.comp hneg).const_smul I)
  have hs := (IntervalIntegrable.trans_iff h0).mp hf
  have heq : VIntegral f x 0 T + VIntegral f x (-T) 0 = VIntegral f x (-T) T := by
    simp only [VIntegral,←smul_add]
    rw [add_comm,intervalIntegral.integral_add_adjacent_intervals hs.1 hs.2]
  change Tendsto (fun ε : ℝ => VIntegral f x ε T + VIntegral f x (-T) (-ε))
    (𝓝 0) (𝓝 (VIntegral f x 0 T + VIntegral f x (-T) 0)) at h
  rw [heq] at h
  exact h.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

end JointDickman

end OAI
