import OAI.Geometry.PeriodicTiling.MarkedTile
import OAI.Geometry.PeriodicTiling.CyclicQuotient
import OAI.Geometry.PeriodicTiling.VoxelMeasure
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile

open MeasureTheory
open scoped Classical

private theorem cast_scale_eq (m : ℕ) (z : Lattice 3) :
    castLattice (scale m z) = scaledCast m z := by
  ext i
  simp [scaledCast, scale]

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

theorem Tstar_subset_T0 : s.Tstar ⊆ s.T0 := Finset.erase_subset _ _

theorem Tstar_subset_T1 (w : Lattice 3) : s.Tstar ⊆ s.T1 w := by
  rw [s.T1_eq_insert w]
  exact Finset.subset_insert _ _

theorem marked_cell_mem_thickening_iff
    {m : ℕ} [NeZero m] (s : ResidueSection m)
    {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0)))
    (F : Finset (Lattice 3)) :
    x - scaledCast m g ∈ Thickening F ↔
      ∃ z ∈ F, scale m g + z = scale m a + s.t0 := by
  have he (z : Lattice 3) :
      x - castLattice (scale m g + z) =
        (x - scaledCast m g) - castLattice z := by
    rw [map_add, cast_scale_eq]
    abel
  constructor
  · rintro ⟨z, hz, hcell⟩
    refine ⟨z, hz, (mem_unitVoxel_cast_iff_of_mem_open hx).mp ?_⟩
    change x - castLattice (scale m g + z) ∈ unitCube 3
    rwa [he z]
  · rintro ⟨z, hz, hcorner⟩
    refine ⟨z, hz, ?_⟩
    have hcell := (mem_unitVoxel_cast_iff_of_mem_open hx).mpr hcorner
    change x - castLattice (scale m g + z) ∈ unitCube 3 at hcell
    rwa [he z] at hcell

theorem marked_cell_T0_iff {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0))) :
    x - scaledCast m g ∈ Thickening s.T0 ↔ g = a := by
  rw [s.marked_cell_mem_thickening_iff hx]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨v, hv⟩ := s.mem_T0.mp hz
    rw [← hv] at he
    have hp : (g, v) = (a, (0 : Residue m)) := by
      apply s.coordinates_injective
      exact he
    exact congrArg Prod.fst hp
  · rintro rfl
    exact ⟨s.t0, s.t0_mem_T0, rfl⟩

theorem marked_cell_T1_iff (w : Lattice 3) {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0))) :
    x - scaledCast m g ∈ Thickening (s.T1 w) ↔ g = a - w := by
  rw [s.marked_cell_mem_thickening_iff hx]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨v, hv⟩ := s.mem_T1.mp hz
    rw [← hv] at he
    have hv0 : v = 0 := by
      have hr := congrArg (residue m) he
      simpa only [map_add, residue_scale, s.residue_t1, s.residue_t0,
        zero_add] using hr
    subst v
    have hga : g + w = a := by
      apply scale_injective m
      apply add_right_cancel (b := s.t0)
      simpa only [t1, ite_eq_left rfl, ite_true, map_add, add_assoc] using he
    exact eq_sub_iff_add_eq.mpr hga
  · rintro rfl
    refine ⟨s.t1 w 0, s.mem_T1.mpr ⟨0, rfl⟩, ?_⟩
    simp only [t1, ite_true]
    rw [← add_assoc, ← map_add, sub_add_cancel]

theorem marked_cell_sources (w : Lattice 3) (B : Set (Lattice 3))
    {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0))) :
    (x - scaledCast m g ∈ if g ∈ B then Thickening (s.T1 w) else Thickening s.T0) ↔
      (g = a ∧ g ∉ B) ∨ (g = a - w ∧ g ∈ B) := by
  by_cases hg : g ∈ B
  · simp only [hg, ite_eq_left, not_true_eq_false, and_false, false_or, and_true,
      s.marked_cell_T1_iff w hx]
  · simp only [hg, ite_false, not_false_eq_true, and_true, and_false, or_false,
      s.marked_cell_T0_iff hx]

theorem period_of_marked_cells (w : Lattice 3) (hw : w ≠ 0)
    (B : Set (Lattice 3))
    (hcover : ∀ᵐ x ∂volume, ∃! g : Lattice 3,
      x - scaledCast m g ∈
        if g ∈ B then Thickening (s.T1 w) else Thickening s.T0) :
    Period B w := by
  have hiff : ∀ a : Lattice 3, a ∈ B ↔ a - w ∈ B := by
    intro a
    have hvol : volume (openUnitVoxel (castLattice (scale m a + s.t0))) ≠ 0 := by
      rw [openUnitVoxel_volume]
      exact one_ne_zero
    obtain ⟨x, hx, hgcover⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hvol (ae_restrict_of_ae hcover)
    obtain ⟨g, hg, huniq⟩ := hgcover
    constructor
    · intro ha
      rcases (s.marked_cell_sources w B hx).mp hg with ⟨hga, hgB⟩ | ⟨hga, hgB⟩
      · exact False.elim (hgB (hga.symm ▸ ha))
      · exact hga ▸ hgB
    · intro haw
      by_contra ha
      have hpa : x - scaledCast m a ∈
          if a ∈ B then Thickening (s.T1 w) else Thickening s.T0 :=
        (s.marked_cell_sources w B hx).mpr (Or.inl ⟨rfl, ha⟩)
      have hpaw : x - scaledCast m (a - w) ∈
          if a - w ∈ B then Thickening (s.T1 w) else Thickening s.T0 :=
        (s.marked_cell_sources w B hx).mpr (Or.inr ⟨rfl, haw⟩)
      have he : a = a - w := (huniq a hpa).trans (huniq (a - w) hpaw).symm
      apply hw
      calc
        w = a - (a - w) := by abel
        _ = a - a := by rw [← he]
        _ = 0 := sub_self a
  intro z
  simpa only [add_sub_cancel_right] using hiff (z + w)

theorem kernel_periods_of_marked_cells (Q : ℕ) [NeZero Q]
    (B : Set (Lattice 3))
    (hcover : ∀ᵐ x ∂volume, ∃! g : Lattice 3,
      x - scaledCast m g ∈ if g ∈ B then
        Thickening (s.T1 (CyclicQuotient.kernelStep Q)) else Thickening s.T0) :
    ∀ k ∈ (CyclicQuotient.projection Q).ker, Period B k := by
  have hw := s.period_of_marked_cells (CyclicQuotient.kernelStep Q)
    (CyclicQuotient.kernelStep_ne_zero Q) B hcover
  intro k hk
  obtain ⟨n, rfl⟩ := (CyclicQuotient.mem_ker_iff_zsmul_kernelStep Q k).mp hk
  exact (periodSubgroup B).zsmul_mem hw n

end ResidueSection
end PeriodicTilingThree.MarkedTile

end

end OAI
