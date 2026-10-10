import OAI.InformationTheory.BooleanNoise.PerspectiveInequality
import OAI.InformationTheory.SoftChannel.PerspectiveCalculus

namespace OAI

section

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

theorem PerspectiveInequality_sq_lt_one_of_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) : b ^ 2 < 1 := by
  have h := mul_pos (sub_pos.mpr hb1) (show 0 < 1 + b by linarith)
  nlinarith

end LeanBlast.CourtadeKumar
end
end

end OAI
