import Mathlib.Tactic

namespace OAI

/-! # Local osmotic-energy control from arbitrary-parameter Li--Yau

The three scalars are the two diagonal logarithmic energies, their mixed
energy, and the retained cutoff error. No energy term is discarded.
-/

namespace RegularPointCoordinates

theorem osmotic_energy_algebra {S E R B α : ℝ} (hα : 1 < α)
    (hLiYau : S ≤ α*(-2*E-B)+R) :
    S+2*E ≤ ((α-1)/(α+1))*(S-2*E)+(2/(α+1))*(R-α*B) := by
  have hpos : 0 < α+1 := by linarith
  apply (mul_le_mul_iff_left₀ hpos).mp
  have he : (((α-1)/(α+1))*(S-2*E)+(2/(α+1))*(R-α*B))*(α+1) =
      (α-1)*(S-2*E)+2*(R-α*B) := by field_simp
  rw [he]
  nlinarith only [hLiYau]

end RegularPointCoordinates

end OAI
