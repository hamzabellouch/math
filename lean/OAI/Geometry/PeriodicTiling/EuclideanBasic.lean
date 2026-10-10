import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.ZLattice.Basic

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open MeasureTheory

@[simp] theorem castLattice_apply {d : ℕ} (z : Lattice d) (i : Fin d) :
    castLattice z i = (z i : ℝ) := rfl

theorem castLattice_injective {d : ℕ} :
    Function.Injective (castLattice : Lattice d → Space d) := by
  intro z w h
  funext i
  exact Int.cast_injective (congrArg (fun x : Space d => x i) h)

def unitVoxel {d : ℕ} (c : Space d) : Set (Space d) :=
  {x | x - c ∈ unitCube d}

theorem mem_unitCube {d : ℕ} {x : Space d} :
    x ∈ unitCube d ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  constructor
  · intro h i
    exact ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

@[simp] theorem mem_unitVoxel {d : ℕ} {c x : Space d} :
    x ∈ unitVoxel c ↔ x - c ∈ unitCube d := Iff.rfl

theorem unitVoxel_eq_Icc {d : ℕ} (c : Space d) :
    unitVoxel c = Set.Icc c (c + 1) := by
  ext x
  constructor
  · intro hx
    have h := mem_unitCube.mp hx
    constructor
    · intro i
      exact sub_nonneg.mp (h i).1
    · intro i
      have hi := (sub_le_iff_le_add.mp (h i).2)
      simpa [add_comm] using hi
  · intro hx
    apply mem_unitCube.mpr
    intro i
    constructor
    · exact sub_nonneg.mpr (hx.1 i)
    · apply sub_le_iff_le_add.mpr
      simpa [add_comm] using hx.2 i

@[simp] theorem mem_Thickening {d : ℕ} {F : Finset (Lattice d)} {x : Space d} :
    x ∈ Thickening F ↔ ∃ z ∈ F, x - castLattice z ∈ unitCube d := Iff.rfl

theorem unitVoxel_subset_Thickening {d : ℕ} {F : Finset (Lattice d)}
    {z : Lattice d} (hz : z ∈ F) : unitVoxel (castLattice z) ⊆ Thickening F := by
  intro x hx
  exact ⟨z, hz, hx⟩

def TypedAETiles {d : ℕ} (Ω0 Ω1 C C1 : Set (Space d)) : Prop := by
  classical
  exact ∀ᵐ x ∂volume, ∃! c : C,
    x - (c : Space d) ∈ if (c : Space d) ∈ C1 then Ω1 else Ω0

def scaledCast {d : ℕ} (m : ℕ) : Lattice d →+ Space d where
  toFun z := (m : ℝ) • castLattice z
  map_zero' := by simp
  map_add' z w := by simp [smul_add]

@[simp] theorem scaledCast_apply {d : ℕ} (m : ℕ) (z : Lattice d) :
    scaledCast m z = (m : ℝ) • castLattice z := rfl

theorem scaledCast_injective {d : ℕ} {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (scaledCast m : Lattice d → Space d) := by
  intro z w h
  funext i
  have hi := congrArg (fun x : Space d => x i) h
  change (m : ℝ) * (z i : ℝ) = (m : ℝ) * (w i : ℝ) at hi
  exact Int.cast_injective (mul_left_cancel₀ (Nat.cast_ne_zero.mpr hm) hi)

def scaledGrid (m : ℕ) : AddSubgroup (Space 3) :=
  (scaledCast m : Lattice 3 →+ Space 3).range

theorem mem_scaledGrid {m : ℕ} {x : Space 3} :
    x ∈ scaledGrid m ↔ ∃ z : Lattice 3, (m : ℝ) • castLattice z = x := Iff.rfl

end PeriodicTilingThree

end

end OAI
