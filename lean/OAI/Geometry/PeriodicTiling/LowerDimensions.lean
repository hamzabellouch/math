import OAI.Geometry.PeriodicTiling.OneDimensionalLattice
import OAI.Geometry.PeriodicTiling.PlanarPeriodicity
import OAI.Geometry.PeriodicTiling.TilingTransport
import Lean.Elab.Tactic.Omega

namespace OAI

namespace PeriodicTilingThree

theorem lattice_two_tile_has_fullyPeriodic_complement
    (F : Finset (Lattice 2)) (h : ∃ A, Tiles F A) :
    ∃ B, Tiles F B ∧ FullyPeriodic B := by
  classical
  obtain ⟨A, hA⟩ := h
  have hPlane := hA.preimage_addEquiv planeEquiv
  obtain ⟨B, hB, hPeriod⟩ := plane_tile_has_fullyPeriodic_complement
    (F.image planeEquiv.symm) hPlane.tile_nonempty ⟨_, hPlane⟩
  refine ⟨planeEquiv '' B, ?_, (fullyPeriodic_image_addEquiv_iff planeEquiv).mpr hPeriod⟩
  have hImage := hB.image_addEquiv planeEquiv
  simpa only [Finset.image_image, Function.comp_def, planeEquiv.apply_symm_apply,
    Finset.image_id'] using hImage

theorem tiles_below_three_have_fullyPeriodic_complements
    (d : ℕ) (hd : d < 3) (F : Finset (Lattice d)) (h : ∃ A, Tiles F A) :
    ∃ B, Tiles F B ∧ FullyPeriodic B := by
  cases d with
  | zero => exact lattice_zero_tile_has_fullyPeriodic_complement F h
  | succ d =>
      cases d with
      | zero => exact lattice_one_tile_has_fullyPeriodic_complement F h
      | succ d =>
          cases d with
          | zero => exact lattice_two_tile_has_fullyPeriodic_complement F h
          | succ d => omega

end PeriodicTilingThree

end OAI
