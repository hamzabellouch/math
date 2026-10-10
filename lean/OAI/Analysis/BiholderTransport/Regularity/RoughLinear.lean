import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ShortEnvelopeSemibound

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma second_fderiv_comp_linear_at {f : F → ℝ} (L : E →L[ℝ] F) {x : E}
    (hnear : ∀ᶠ y in 𝓝 (L x),DifferentiableAt ℝ f y)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (L x)) (d e : E) :
    fderiv ℝ (fderiv ℝ (fun q=>f (L q))) x d e=
      fderiv ℝ (fderiv ℝ f) (L x) (L d) (L e) := by
  have hl : (fderiv ℝ L)=(fun _ : E=>L) := by funext q; exact L.fderiv
  have H := second_fderiv_comp_at hnear hf (L.contDiff (n := 2)).contDiffAt d e
  rw [hl] at H
  have hz : fderiv ℝ (fun _ : E => L) x = 0 := fderiv_const_apply L
  rw [hz] at H
  simpa using H
end WeakMTWTransport

end

end OAI
