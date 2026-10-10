import OAI.Geometry.PeriodicTiling.EuclideanBasic
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory

def openUnitVoxel {d : ℕ} (c : Space d) : Set (Space d) :=
  Set.pi Set.univ (fun i => Set.Ioo (c i) (c i + 1))

theorem mem_openUnitVoxel {d : ℕ} {c x : Space d} :
    x ∈ openUnitVoxel c ↔ ∀ i, c i < x i ∧ x i < c i + 1 := by
  simp [openUnitVoxel, Set.mem_pi]

theorem openUnitVoxel_nonempty {d : ℕ} (c : Space d) :
    (openUnitVoxel c).Nonempty := by
  refine ⟨fun i => c i + 1 / 2, mem_openUnitVoxel.mpr ?_⟩
  intro i
  constructor <;> linarith

theorem isOpen_openUnitVoxel {d : ℕ} (c : Space d) :
    IsOpen (openUnitVoxel c) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

theorem openUnitVoxel_subset {d : ℕ} (c : Space d) :
    openUnitVoxel c ⊆ unitVoxel c := by
  intro x hx
  rw [unitVoxel_eq_Icc]
  have h := mem_openUnitVoxel.mp hx
  exact ⟨fun i => (h i).1.le, fun i => (h i).2.le⟩

theorem unitVoxel_isCompact {d : ℕ} (c : Space d) :
    IsCompact (unitVoxel c) := by
  rw [unitVoxel_eq_Icc]
  exact isCompact_Icc

theorem unitVoxel_isClosed {d : ℕ} (c : Space d) :
    IsClosed (unitVoxel c) := (unitVoxel_isCompact c).isClosed

theorem unitVoxel_measurableSet {d : ℕ} (c : Space d) :
    MeasurableSet (unitVoxel c) := (unitVoxel_isClosed c).measurableSet

theorem unitVoxel_inter_eq_Icc {d : ℕ} (a b : Space d) :
    unitVoxel a ∩ unitVoxel b =
      Set.Icc (fun i => max (a i) (b i))
        (fun i => min (a i + 1) (b i + 1)) := by
  rw [unitVoxel_eq_Icc, unitVoxel_eq_Icc]
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun i => max_le (ha.1 i) (hb.1 i),
      fun i => le_min (ha.2 i) (hb.2 i)⟩
  · rintro ⟨hl, hu⟩
    exact ⟨⟨fun i => (le_max_left _ _).trans (hl i),
      fun i => (hu i).trans (min_le_left _ _)⟩,
      ⟨fun i => (le_max_right _ _).trans (hl i),
      fun i => (hu i).trans (min_le_right _ _)⟩⟩

theorem mem_unitVoxel_cast_iff_of_mem_open {d : ℕ} {x : Space d}
    {z z' : Lattice d} (hx : x ∈ openUnitVoxel (castLattice z)) :
    x ∈ unitVoxel (castLattice z') ↔ z' = z := by
  constructor
  · intro hx'
    have ho := mem_openUnitVoxel.mp hx
    rw [unitVoxel_eq_Icc] at hx'
    funext i
    have hi := ho i
    have hl := hx'.1 i
    have hu := hx'.2 i
    change (z i : ℝ) < x i ∧ x i < (z i : ℝ) + 1 at hi
    change (z' i : ℝ) ≤ x i at hl
    change x i ≤ (z' i : ℝ) + 1 at hu
    rcases lt_trichotomy (z' i) (z i) with hlt | heq | hgt
    · have hh : (z' i : ℝ) + 1 ≤ (z i : ℝ) := by
        have hh' : ((z' i + 1 : ℤ) : ℝ) ≤ (z i : ℝ) :=
          Int.cast_le.mpr (Int.add_one_le_of_lt hlt)
        simpa only [Int.cast_add, Int.cast_one] using hh'
      linarith
    · exact heq
    · have hh : (z i : ℝ) + 1 ≤ (z' i : ℝ) := by
        have hh' : ((z i + 1 : ℤ) : ℝ) ≤ (z' i : ℝ) :=
          Int.cast_le.mpr (Int.add_one_le_of_lt hgt)
        simpa only [Int.cast_add, Int.cast_one] using hh'
      linarith
  · rintro rfl
    exact openUnitVoxel_subset _ hx

theorem openUnitVoxel_disjoint_unitVoxel_int {d : ℕ} {z z' : Lattice d}
    (hne : z ≠ z') :
    Disjoint (openUnitVoxel (castLattice z)) (unitVoxel (castLattice z')) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  exact hne ((mem_unitVoxel_cast_iff_of_mem_open hx).mp hx').symm

end PeriodicTilingThree

end

end OAI
