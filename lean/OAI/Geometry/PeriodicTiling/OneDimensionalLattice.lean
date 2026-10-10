import OAI.Geometry.PeriodicTiling.LatticeDimensions
import OAI.Geometry.PeriodicTiling.OneDimensional
import OAI.Geometry.PeriodicTiling.TilingTransport

namespace OAI

namespace PeriodicTilingThree

theorem fullyPeriodic_of_tiles_lattice_one
    {F : Finset (Lattice 1)} {A : Set (Lattice 1)} (h : Tiles F A) :
    FullyPeriodic A := by
  have hInt := h.preimage_addEquiv intEquiv
  have hPeriod := fullyPeriodic_of_tiles_int _ hInt.tile_nonempty _ hInt
  exact (fullyPeriodic_preimage_addEquiv_iff intEquiv).mp hPeriod

theorem lattice_one_tile_has_fullyPeriodic_complement
    (F : Finset (Lattice 1)) (h : ∃ A, Tiles F A) :
    ∃ A, Tiles F A ∧ FullyPeriodic A := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA, fullyPeriodic_of_tiles_lattice_one hA⟩

end PeriodicTilingThree

end OAI
