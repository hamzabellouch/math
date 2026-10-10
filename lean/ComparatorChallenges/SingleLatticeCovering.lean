import Mathlib

namespace OAI

/-! Convex bodies and exact coverings by a single lattice in real coordinate space. -/

namespace SingleLatticeCovering

open MeasureTheory
open scoped Pointwise

abbrev Space (n : ℕ) := Fin n → ℝ

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def LatticeCovers {n : ℕ} (K : Set (Space n)) (L : Submodule ℤ (Space n)) : Prop :=
  K + (L : Set (Space n)) = Set.univ

theorem single_lattice_covering :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Set (Space n)), IsConvexBody K →
        ∃ (L : Submodule ℤ (Space n)) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ LatticeCovers K L ∧
            (volume K).toReal / ZLattice.covolume L ≤ C * (n : ℝ) * Real.log (n : ℝ) := by sorry

end SingleLatticeCovering

end OAI
