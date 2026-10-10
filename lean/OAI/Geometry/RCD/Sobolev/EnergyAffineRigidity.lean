import Mathlib.Tactic

namespace OAI

/-! # Exact cancellation of the recovery energy leaves a vanishing mixed term -/

namespace RegularPointCoordinates

theorem energy_affine_rigidity {E M P B : ℝ}
    (h : ∀ t : ℝ, E+2*t*B+t^2*P≤M+t^2*P) : B=0 := by
  by_contra hb
  have he : 2*((M-E+1)/(2*B))*B=M-E+1 := by
    field_simp [hb]
  have hh := h ((M-E+1)/(2*B))
  nlinarith

end RegularPointCoordinates

end OAI
