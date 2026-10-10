import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma reciprocal_inverses {A R : F →L[ℝ] E} {B L : E →L[ℝ] F}
    (hAB : ∀ d k, inner ℝ (A d) k=inner ℝ d (B k))
    (hAL : ∀ v, A (L v)=v) (hBR : ∀ w, B (R w)=w) (v:E) (w:F) :
    inner ℝ (L v) w=inner ℝ v (R w) := by
  have H := hAB (L v) (R w)
  rw [hAL,hBR] at H
  exact H.symm

end WeakMTWTransport

end

end OAI
