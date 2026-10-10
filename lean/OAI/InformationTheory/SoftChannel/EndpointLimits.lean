import OAI.InformationTheory.BooleanNoise.EndpointLimits
import OAI.InformationTheory.BooleanNoise.EntropyBounds
import OAI.InformationTheory.BooleanNoise.InverseScalars
import OAI.InformationTheory.SoftChannel.Thinning

namespace OAI

section

noncomputable section

open Filter Set
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem EndpointLimits_endpoint_one_sub_sq_pos {u : ℝ} (hu : u ∈ Ioo 0 1) :
    0 < 1 - u ^ 2 := by
  have h := mul_pos (show 0 < 1 + u by linarith [hu.1]) (sub_pos.mpr hu.2)
  nlinarith

end LeanBlast.CourtadeKumar
end
end

end OAI
