import OAI.Geometry.PeriodicTiling.CyclicCounterexample
import OAI.Geometry.PeriodicTiling.ThreeDimensionalTransfer

namespace OAI

namespace PeriodicTilingThree

theorem exists_three_dimensional_tile :
    ∃ T : Finset (Lattice 3),
      T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3), AETiles (Thickening T) A →
        ¬ EuclideanFullyPeriodic A) := by
  obtain ⟨Q, hQ, F, hF, htile, haperiodic⟩ := exists_cyclic_counterexample
  let : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  exact three_dimensional_tile_of_cyclic_counterexample Q F hF htile haperiodic

end PeriodicTilingThree

end OAI
