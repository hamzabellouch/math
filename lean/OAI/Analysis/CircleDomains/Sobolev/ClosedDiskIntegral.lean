import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Outer circles have zero plane area; the source density integral is
unchanged when the outer disk is closed. -/
open Set Function Filter MeasureTheory Metric
noncomputable section
namespace CircleDomainRigidity

 theorem integral_inter_closedBall_eq_ball (U : Set ℂ) (c : ℂ) (r : ℝ) (q : ℂ → ℝ) :
    (∫ z in U ∩ closedBall c r, q z) = ∫ z in U ∩ ball c r, q z := by
  apply setIntegral_congr_set
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume c r)] with z hz
  apply propext
  have hne : dist z c ≠ r := hz
  simp only [mem_inter_iff,mem_closedBall,mem_ball]
  exact and_congr_right (fun _ => ⟨fun h => lt_of_le_of_ne h hne,fun h => h.le⟩)

end CircleDomainRigidity

end

end OAI
