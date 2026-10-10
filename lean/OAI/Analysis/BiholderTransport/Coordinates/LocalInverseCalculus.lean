import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma local_inverse_derivative {e : F → E} {L : E → F} {p : E}
    (he : DifferentiableAt ℝ e (L p)) (hL : DifferentiableAt ℝ L p)
    (hid : (fun v => e (L v)) =ᶠ[𝓝 p] (fun v => v)) (v : E) :
    fderiv ℝ e (L p) (fderiv ℝ L p v)=v := by
  have H := hid.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp p he hL,fderiv_fun_id] at H
  exact congrArg (fun A : E →L[ℝ] E => A v) H


end WeakMTWTransport
end

end OAI
