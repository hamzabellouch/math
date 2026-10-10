import OAI.Geometry.PeriodicTiling.TilingTranslation
import OAI.Geometry.PeriodicTiling.RigidSectionGeometry
import OAI.Geometry.PeriodicTiling.MarkedTileExistence
import OAI.Geometry.PeriodicTiling.MarkedTileDescent
import OAI.Geometry.PeriodicTiling.LatticeThickening
import OAI.Geometry.PeriodicTiling.LatticePeriodicity

namespace OAI

noncomputable section

namespace PeriodicTilingThree

theorem three_dimensional_tile_of_cyclic_counterexample
    (Q : ℕ) [NeZero Q] (F : Finset (CyclicQuotient.Group Q))
    (hF : F.Nonempty) (htile : ∃ A, Tiles F A)
    (haperiodic : ∀ A, Tiles F A → ¬ FullyPeriodic A) :
    ∃ T : Finset (Lattice 3),
      T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3), AETiles (Thickening T) A →
        ¬ EuclideanFullyPeriodic A) := by
  classical
  obtain ⟨F₀, hF₀, ⟨B, hB⟩, hBaperiodic⟩ :=
    exists_zero_mem_normalization F hF htile haperiodic
  let T : Finset (Lattice 3) := rigidSection.finalTile
    (CyclicQuotient.kernelStep Q) (CyclicQuotient.representatives Q F₀)
  let C : Set (Lattice 3) :=
    (MarkedTile.scale 64) '' ((CyclicQuotient.projection Q) ⁻¹' B)
  have hT : Tiles T C := rigidSection.cyclic_finalTile_tiles Q hB
  have hreal : ∀ A : Set (Space 3),
      AETiles (Thickening T) A → ¬ EuclideanFullyPeriodic A := by
    intro A hA
    exact rigidSection.no_euclideanFullyPeriodic (by norm_num)
      rigidSection_rigidDifferences Q F₀ hF₀ hBaperiodic hA
  refine ⟨T, hT.tile_nonempty, ⟨C, hT⟩, ?_,
    ⟨castLattice '' C, hT.aeTiles_thickening⟩, hreal⟩
  intro A hA hperiodic
  exact hreal (castLattice '' A) hA.aeTiles_thickening hperiodic.castLattice_image

end PeriodicTilingThree

end

end OAI
