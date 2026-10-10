import OAI.Geometry.RCD.Coordinates.PatchAssembly

namespace OAI

/-! # Enlarging the permissible error of unchanged patch data -/

open Set
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Only the allowed mass and energy budget changes; all constructed
patches, operators and frozen frames are retained exactly. -/
def PatchIterationGeometry.monoError {Ω : Set E} {r0 Theta epsilon delta : ℝ}
    {N : ℕ} {C K L : ℝ} (g : PatchIterationGeometry (ι := ι) Ω r0 Theta epsilon N C K L)
    (h : epsilon ≤ delta) : PatchIterationGeometry (ι := ι) Ω r0 Theta delta N C K L :=
  { g with
    energy_budget := fun k x hx => (g.energy_budget k x hx).trans h
    mass_small := fun i x hx xi => (g.mass_small i x hx xi).trans
      (mul_le_mul_of_nonneg_right h (sq_nonneg ‖g.frozen i x xi‖)) }

end RegularPointCoordinates

end

end OAI
