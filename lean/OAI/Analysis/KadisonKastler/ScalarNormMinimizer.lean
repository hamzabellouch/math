import OAI.Analysis.KadisonKastler.PublishedDixmier
import Mathlib.Topology.Order.Compact

namespace OAI

/-! # A nearest scalar operator in the ambient norm -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Compactness of a scalar disk gives a nearest scalar operator. -/
theorem exists_scalar_norm_minimizer (a : H →L[ℂ] H) :
    ∃ z : ℂ, ∀ w : ℂ, ‖a - z • (1 : H →L[ℂ] H)‖ ≤ ‖a - w • 1‖ := by
  let R : ℝ := 2 * ‖a‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_self] using hR
  have hf : Continuous (fun z : ℂ => ‖a - z • (1 : H →L[ℂ] H)‖) := by
    fun_prop
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMinOn
    ⟨0, hzero⟩ hf.continuousOn
  refine ⟨z, fun w => ?_⟩
  by_cases hw : w ∈ Metric.closedBall (0 : ℂ) R
  · exact hz hw
  have hz0 : ‖a - z • (1 : H →L[ℂ] H)‖ ≤ ‖a‖ := by
    have h0 := hz hzero
    change ‖a - z • (1 : H →L[ℂ] H)‖ ≤ ‖a - (0 : ℂ) • 1‖ at h0
    simpa only [zero_smul, sub_zero] using h0
  have hwR : R < ‖w‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hw
  have hwbound : ‖w‖ ≤ ‖a‖ + ‖a - w • (1 : H →L[ℂ] H)‖ := by
    have he : w • (1 : H →L[ℂ] H) = a - (a - w • 1) := by abel
    calc
      ‖w‖ = ‖w • (1 : H →L[ℂ] H)‖ := by simp
      _ ≤ ‖a‖ + ‖a - w • (1 : H →L[ℂ] H)‖ := by
        conv_lhs => rw [he]
        exact norm_sub_le _ _
  dsimp [R] at hwR
  linarith

end

end KadisonKastler

end OAI
