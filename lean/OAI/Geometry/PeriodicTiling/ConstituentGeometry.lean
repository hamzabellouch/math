import OAI.Geometry.PeriodicTiling.MarkedTile
import OAI.Geometry.PeriodicTiling.VoxelMeasure
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile

open Set MeasureTheory

@[simp] theorem castLattice_scale (m : ℕ) (u : Lattice 3) :
    castLattice (scale m u) = scaledCast m u := by
  ext i
  simp [scale, scaledCast, castLattice]

def center (m : ℕ) (a : Space 3) (u : Lattice 3) : Space 3 :=
  a + scaledCast m u

@[simp] theorem center_zero (m : ℕ) (a : Space 3) : center m a 0 = a := by
  simp [center]

def centers (m : ℕ) (U : Finset (Lattice 3)) (A : Set (Space 3)) : Set (Space 3) :=
  Set.range (fun q : A × ↥U => center m q.1 q.2)

theorem mem_centers {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    {c : Space 3} : c ∈ centers m U A ↔ ∃ a ∈ A, ∃ u ∈ U, center m a u = c := by
  constructor
  · rintro ⟨⟨a, u⟩, h⟩
    exact ⟨a, a.property, u, u.property, h⟩
  · rintro ⟨a, ha, u, hu, h⟩
    exact ⟨(⟨a, ha⟩, ⟨u, hu⟩), h⟩

theorem subset_centers {m : ℕ} {U : Finset (Lattice 3)} (h0 : 0 ∈ U)
    (A : Set (Space 3)) : A ⊆ centers m U A := by
  intro a ha
  exact mem_centers.mpr ⟨a, ha, 0, h0, center_zero m a⟩

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

def constituent (w u : Lattice 3) : Finset (Lattice 3) :=
  if u = 0 then s.T1 w else s.T0

def part (w u : Lattice 3) : Finset (Lattice 3) :=
  (s.constituent w u).image (fun t => scale m u + t)

theorem mem_part {w u z : Lattice 3} :
    z ∈ s.part w u ↔ ∃ v, s.point w u v = z := by
  classical
  by_cases hu : u = 0
  · subst u
    simp [part, constituent, mem_T1]
  · simp only [part, constituent, hu, ite_false, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, he⟩
      obtain ⟨v, rfl⟩ := s.mem_T0.mp ht
      exact ⟨v, by simpa only [s.point_of_ne_zero w hu] using he⟩
    · rintro ⟨v, hv⟩
      exact ⟨s.t v, s.mem_T0.mpr ⟨v, rfl⟩,
        by simpa only [s.point_of_ne_zero w hu] using hv⟩

theorem part_subset_finalTile {w : Lattice 3} {U : Finset (Lattice 3)}
    {u : Lattice 3} (hu : u ∈ U) : s.part w u ⊆ s.finalTile w U := by
  intro z hz
  obtain ⟨v, hv⟩ := s.mem_part.mp hz
  exact s.mem_finalTile.mpr ⟨u, hu, v, hv⟩

theorem parts_disjoint {w : Lattice 3} {U : Finset (Lattice 3)} (hw : w ∉ U)
    {u u' : ↥U} (hne : u ≠ u') : Disjoint (s.part w u) (s.part w u') := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨v, hv⟩ := s.mem_part.mp hz
  obtain ⟨v', hv'⟩ := s.mem_part.mp hz'
  have hp : (u, v) = (u', v') := s.point_injective hw (hv.trans hv'.symm)
  exact hne (congrArg Prod.fst hp)

theorem mem_thickening_part {w u : Lattice 3} {x : Space 3} :
    x ∈ Thickening (s.part w u) ↔
      x - scaledCast m u ∈ Thickening (s.constituent w u) := by
  classical
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨t, ht, ?_⟩
    simpa only [map_add, castLattice_scale, sub_add_eq_sub_sub] using hx
  · rintro ⟨t, ht, hx⟩
    refine ⟨scale m u + t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    simpa only [map_add, castLattice_scale, sub_add_eq_sub_sub] using hx

theorem mem_translated_part {w u : Lattice 3} {a x : Space 3} :
    x - a ∈ Thickening (s.part w u) ↔
      x - center m a u ∈ Thickening (s.constituent w u) := by
  simpa only [center, sub_add_eq_sub_sub] using
    (s.mem_thickening_part (w := w) (u := u) (x := x - a))

theorem mem_thickening_finalTile {w : Lattice 3} {U : Finset (Lattice 3)}
    {x : Space 3} :
    x ∈ Thickening (s.finalTile w U) ↔
      ∃ u : ↥U, x ∈ Thickening (s.part w u) := by
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨u, hu, v, hv⟩ := s.mem_finalTile.mp hz
    exact ⟨⟨u, hu⟩, z, s.mem_part.mpr ⟨v, hv⟩, hx⟩
  · rintro ⟨u, z, hz, hx⟩
    exact ⟨z, s.part_subset_finalTile u.property hz, hx⟩

theorem mem_translated_finalTile {w : Lattice 3} {U : Finset (Lattice 3)}
    {a x : Space 3} :
    x - a ∈ Thickening (s.finalTile w U) ↔
      ∃ u : ↥U, x - center m a u ∈ Thickening (s.constituent w u) := by
  rw [s.mem_thickening_finalTile]
  exact exists_congr fun u => s.mem_translated_part

theorem Tstar_subset_constituent (w u : Lattice 3) :
    s.Tstar ⊆ s.constituent w u := by
  classical
  intro z hz
  by_cases hu : u = 0
  · simp only [constituent, hu, ite_true, s.T1_eq_insert]
    exact Finset.mem_insert_of_mem hz
  · simpa only [constituent, hu, ite_false] using (Finset.mem_erase.mp hz).2

theorem Tstar_nonempty (hm : 2 ≤ m) : s.Tstar.Nonempty := by
  apply Finset.card_pos.mp
  rw [s.card_Tstar]
  have hp := Nat.pow_le_pow_left hm 3
  exact Nat.sub_pos_of_lt ((by decide : 1 < 2 ^ 3).trans_le hp)

theorem common_voxel_subset_constituent (w u : Lattice 3) (a : Space 3)
    {t : Lattice 3} (ht : t ∈ s.Tstar) :
    unitVoxel (center m a u + castLattice t) ⊆
      {x | x - center m a u ∈ Thickening (s.constituent w u)} := by
  intro x hx
  refine ⟨t, s.Tstar_subset_constituent w u ht, ?_⟩
  simpa only [mem_unitVoxel, sub_add_eq_sub_sub] using hx

end ResidueSection
end PeriodicTilingThree.MarkedTile

end

end OAI
