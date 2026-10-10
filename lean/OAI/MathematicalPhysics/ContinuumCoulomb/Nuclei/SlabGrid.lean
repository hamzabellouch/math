import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredGrid

namespace OAI

/-! The finite integer grid used for the rectangular slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def slabGridIndices (N M : ℕ) : Finset (Fin 3 → ℤ) := centeredGridIndices ![N,N,M]

theorem slabGrid_covers (N M : ℕ) {h : ℝ} (hh : 0 < h) :
    (⋃ k : {k // k ∈ slabGridIndices N M}, positionCube (gaussCellCenter h k.val) h) =
      slabDomain (((N:ℝ)+1/2)*h) (((M:ℝ)+1/2)*h) := by
  rw [slabGridIndices,centeredGrid_covers _ hh]
  ext x
  change (∀ i : Fin 3, |x i| ≤ ((![N,N,M] i:ℝ)+1/2)*h) ↔ _
  constructor
  · intro hx
    exact ⟨hx 0,hx 1,hx 2⟩
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

end ContinuumCoulomb

end

end OAI
