import Mathlib
import OAI.Analysis.BiholderTransport.Contact.Subgradient

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasQuadraticExpansion_iff_isLittleO {f : E → ℝ} {p : E} {A : E →L[ℝ] E} :
    HasQuadraticExpansion f p A ↔
      (fun h => f h - quadraticTaylor (f 0) p A h) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro H c hc
    obtain ⟨d,hd,hbound⟩ := H c hc
    filter_upwards [Metric.ball_mem_nhds (0:E) hd] with h hh
    simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      hbound h (by simpa only [Metric.mem_ball,dist_zero_right] using hh)
  · intro H c hc
    obtain ⟨d,hd,hbound⟩ := Metric.mem_nhds_iff.mp (H hc)
    refine ⟨d,hd,?_⟩
    intro h hh
    simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      hbound (show h ∈ Metric.ball (0:E) d by simpa only [Metric.mem_ball,dist_zero_right] using hh)
end Inner
end WeakMTWTransport

end

end

end

end OAI
