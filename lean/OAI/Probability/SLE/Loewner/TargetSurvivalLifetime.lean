import OAI.Probability.SLE.Loewner.TargetSurvivalExtension
import OAI.Probability.SLE.Loewner.TargetInverseProperties
import OAI.Probability.SLE.Loewner.RawSurvivingMonotone
import OAI.Probability.SLE.Loewner.OpenSurvivalLifetime

namespace OAI

/-! Every raw point lost by a finite time has a positive finite lifetime,
and survives precisely the earlier nonnegative times. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge.Target

lemma surviving_zero (κ : ℝ) (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    Surviving κ b z 0 := by
  obtain ⟨j,hj,hjz⟩ := Real.exists_nat_pos_inv_lt (show 0 < z.im from hz)
  refine ⟨j,hj,?_⟩
  simpa only [Icc_self,image_singleton,cutoffFlow_zero κ b j hj,csInf_singleton] using hjz

theorem exists_survival_lifetime (κ : ℝ) (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane)
    {T : ℝ} (hT : 0 ≤ T) (hdead : ¬Surviving κ b z T) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧ ∀ t, 0 ≤ t → (Surviving κ b z t ↔ t < τ) := by
  exact exists_open_survival_lifetime (Surviving κ b z) (surviving_zero κ b z hz)
    (fun s t hs hst h => surviving_of_le_time κ b z hs hst h)
    (fun _ ht h => exists_later_survival κ b z ht h) hT hdead

end SLEExactGauge.Target

end

end OAI
