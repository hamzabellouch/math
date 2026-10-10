import OAI.Geometry.PeriodicTiling.SeparatedCenters
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Countable

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory

theorem AETiles.eq_of_voxel_close {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Space d)} (h : AETiles (Thickening F) A)
    {z : Lattice d} (hz : z ∈ F) {a b : A}
    (hc : ∀ i, |(b : Space d) i - (a : Space d) i| < 1) : a = b := by
  by_contra hne
  have hpos := unitVoxel_inter_volume_pos
    ((a : Space d) + castLattice z) ((b : Space d) + castLattice z) (by
      intro i
      simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using hc i)
  have hsub : ∀ c : A, unitVoxel ((c : Space d) + castLattice z) ⊆
      {x | x - (c : Space d) ∈ Thickening F} := by
    intro c x hx
    refine ⟨z, hz, ?_⟩
    simpa only [mem_unitVoxel, sub_add_eq_sub_sub] using hx
  have hnull := (h.aedisjoint hne).mono (hsub a) (hsub b)
  exact (ne_of_gt hpos) hnull

theorem AETiles.floor_injective {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Space d)} (h : AETiles (Thickening F) A) (hF : F.Nonempty) :
    Function.Injective (fun a : A => (fun i => ⌊(a : Space d) i⌋ : Lattice d)) := by
  obtain ⟨z, hz⟩ := hF
  intro a b he
  apply h.eq_of_voxel_close hz
  intro i
  have hi : ⌊(a : Space d) i⌋ = ⌊(b : Space d) i⌋ := congrFun he i
  have ha := Int.floor_le ((a : Space d) i)
  have ha' := Int.lt_floor_add_one ((a : Space d) i)
  have hb := Int.floor_le ((b : Space d) i)
  have hb' := Int.lt_floor_add_one ((b : Space d) i)
  rw [hi] at ha ha'
  apply abs_lt.mpr
  constructor <;> linarith

theorem AETiles.countable_of_thickening {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Space d)} (h : AETiles (Thickening F) A) (hF : F.Nonempty) :
    A.Countable :=
  Set.countable_coe_iff.mp (h.floor_injective hF).countable

end PeriodicTilingThree

end

end OAI
