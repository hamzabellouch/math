import OAI.Geometry.PeriodicTiling.LowerDimensions
import OAI.Geometry.PeriodicTiling.ThreeDimensions

namespace OAI

namespace PeriodicTilingThree

theorem least_lattice_dimension_three :
    IsLeast {d : ℕ | HasTileWithoutPeriodicComplement d} 3 := by
  classical
  constructor
  · obtain ⟨T, hT, hTiles, hNoPeriod, _hRealTiles, _hNoRealPeriod⟩ :=
      exists_three_dimensional_tile
    exact ⟨T, hT, hTiles, hNoPeriod⟩
  · intro d hd
    by_contra hnot
    have hlt : d < 3 := Nat.lt_of_not_ge hnot
    obtain ⟨T, _hT, hTiles, hNoPeriod⟩ := hd
    obtain ⟨A, hA, hPeriod⟩ :=
      tiles_below_three_have_fullyPeriodic_complements d hlt T hTiles
    exact hNoPeriod A hA hPeriod

theorem periodic_tiling_counterexample_and_minimality :
    (∃ T : Finset (Lattice 3), T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3),
        AETiles (Thickening T) A → ¬ EuclideanFullyPeriodic A)) ∧
    IsLeast {d : ℕ | HasTileWithoutPeriodicComplement d} 3 :=
  ⟨exists_three_dimensional_tile, least_lattice_dimension_three⟩

end PeriodicTilingThree

end OAI
