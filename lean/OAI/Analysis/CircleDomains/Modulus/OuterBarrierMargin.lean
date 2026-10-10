import OAI.Analysis.CircleDomains.Transfer.ModelExteriorEstimate
import OAI.Analysis.CircleDomains.Transfer.ModelPairWorkingError

namespace OAI

/-! Strict separation from every trace center on the fixed outer
source collar, from the genuine exterior and vertical error estimates. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem outer_pair_margin {P H z c : EuclideanPlane} {a e C r η : ℝ}
    (hPH : ‖P-H‖ ≤ e) (hHz : ‖H-z‖ ≤ a) (hc : ‖c‖ ≤ C)
    (hz : r+η+e+a+C ≤ ‖z‖) : r+η ≤ ‖P-c‖ := by
  have h₁ : ‖z‖ ≤ ‖z-H‖+‖H‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z-H) H
  have h₂ : ‖H‖ ≤ ‖H-P‖+‖P-c‖+‖c‖ := by
    have hh := norm_add_le (H-P) ((P-c)+c)
    simpa only [sub_add_cancel, add_assoc] using hh.trans
      (add_le_add le_rfl (norm_add_le (P-c) c))
  rw [norm_sub_rev z H] at h₁
  rw [norm_sub_rev H P] at h₂
  linarith

end CircleDomainRigidity

end

end OAI
