import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.MetricSpace.Isometry

namespace OAI

noncomputable section

namespace Tingley

universe u v

abbrev UnitSphere (X : Type u) [NormedAddCommGroup X] := {x : X // ‖x‖ = 1}

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def normalize (x : X) (hx : x ≠ 0) : UnitSphere X :=
  ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx⟩

end Tingley

end

end OAI
