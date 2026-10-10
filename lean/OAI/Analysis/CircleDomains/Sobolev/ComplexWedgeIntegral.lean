import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorWedge
import OAI.Analysis.CircleDomains.Selection.ParallelLineIntegration

namespace OAI

/-! The area contribution to the Stokes estimate has the sharp factor
sqrt(pi) times the containing radius. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem integral_complexCovector_wedge_le
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) {R : ℝ} (hR : 0 ≤ R)
    (hbounded : Ω ⊆ closedBall 0 R)
    (A B : ℂ → ℂ →L[ℝ] ℝ) (hA : ContinuousOn A Ω) (hB : ContinuousOn B Ω)
    (hB2 : MemLp B 2 (volume.restrict Ω))
    (hA1 : ∀ z ∈ Ω, ‖A z‖ ≤ 1) :
    |∫ z in Ω, A z 1 * B z Complex.I - A z Complex.I * B z 1| ≤
      Real.sqrt Real.pi * R * Real.sqrt (∫ z in Ω, ‖B z‖ ^ 2) := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hbounded).trans_lt measure_closedBall_lt_top).ne
  have hnorm : Integrable (fun z => ‖B z‖) (volume.restrict Ω) :=
    hB2.norm.integrable (by norm_num)
  have hcont : ContinuousOn (fun z => A z 1 * B z Complex.I - A z Complex.I * B z 1) Ω :=
    ((hA.clm_apply continuousOn_const).mul (hB.clm_apply continuousOn_const)).sub
      ((hA.clm_apply continuousOn_const).mul (hB.clm_apply continuousOn_const))
  have hbound : ∀ᵐ z ∂(volume.restrict Ω),
      ‖A z 1 * B z Complex.I - A z Complex.I * B z 1‖ ≤ ‖B z‖ := by
    filter_upwards [ae_restrict_mem hΩ] with z hz
    rw [Real.norm_eq_abs]
    exact (complexCovector_wedge_bound (A z) (B z)).trans
      ((mul_le_mul_of_nonneg_right (hA1 z hz) (norm_nonneg _)).trans_eq (one_mul _))
  have hi := hnorm.mono' (hcont.aestronglyMeasurable hΩ) hbound
  have hm : Real.sqrt ((volume.restrict Ω).real univ) ≤ Real.sqrt Real.pi * R := by
    have hm' : (volume.restrict Ω).real univ ≤ Real.pi * R ^ 2 := by
      rw [Measure.real, Measure.restrict_apply_univ]
      exact (measureReal_mono hbounded measure_closedBall_lt_top.ne).trans_eq
        (real_volume_closedBall 0 hR)
    exact (Real.sqrt_le_sqrt hm').trans_eq (by rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR])
  calc
    _ ≤ ∫ z in Ω, ‖A z 1 * B z Complex.I - A z Complex.I * B z 1‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => A z 1 * B z Complex.I - A z Complex.I * B z 1)
    _ ≤ ∫ z in Ω, ‖B z‖ := integral_mono_ae hi.norm hnorm hbound
    _ ≤ Real.sqrt ((volume.restrict Ω).real univ) *
        Real.sqrt (∫ z in Ω, ‖B z‖ ^ 2) :=
      integral_le_sqrt_measure_mul_L2 hB2.norm (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := by gcongr

end CircleDomainRigidity

end

end OAI
