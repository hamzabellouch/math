import OAI.Geometry.CylinderCovering.Nilpotent.RateAssembly
import OAI.Geometry.CylinderCovering.Nilpotent.SmoothProducer

namespace OAI

noncomputable section
namespace CylinderCovering.NilpotentRate

theorem smoothRate : SmoothRateStatement := by
  apply assemble_smooth_rate
  intro D G h hD hG
  obtain ⟨M, K, W, δ₀, hM, hK, hW, hδ₀, hδ₀1, _, hdata⟩ :=
    bounded_second_coarse_data (D := D) (G := G) h hD hG
  refine ⟨M, K, W, δ₀, hM, hK, hW, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hint, han⟩ := hdata δ hδ hδsmall
  refine ⟨hint, ?_⟩
  intro i x hx
  exact ⟨(han i x hx).1, fun b hb => ⟨((han i x hx).2 b hb).1, ((han i x hx).2 b hb).2.2⟩⟩

end CylinderCovering.NilpotentRate

end

end OAI
