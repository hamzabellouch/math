import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Taylor
import OAI.Analysis.BiholderTransport.Coordinates.Inner

namespace OAI

section

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section MintySign
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasQuadraticExpansion.neg {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f p A) : HasQuadraticExpansion (fun q => -f q) (-p) (-A) := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hf ⊢
  convert! hf.const_mul_left (-1:ℝ) using 1
  funext q
  simp only [quadraticTaylor,neg_apply,inner_neg_left]
  ring

lemma HasQuadraticExpansion.nonneg_of_localMin {f : E → ℝ} {A : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f 0 A) (hmin : IsLocalMin f 0) (e : E) :
    0 ≤ inner ℝ (A e) e := by
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhds_iff.mp hmin
  have H := hf.neg.hessian_le_of_upper_support (eta := 0) hr (by
    intro q hq
    have hq' := hh (show q∈Metric.ball (0:E) r by simpa only [Metric.mem_ball,dist_zero_right] using hq)
    simpa only [neg_zero,inner_zero_left,add_zero,zero_div,zero_mul] using neg_le_neg hq') e
  simpa only [neg_apply,inner_neg_left,zero_mul,neg_nonpos] using H
end MintySign
end WeakMTWTransport

end

end

end

end OAI
