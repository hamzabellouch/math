import OAI.Geometry.PeriodicTiling.LatticePeriodicity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open MeasureTheory

def floorLattice {d : ℕ} (x : Space d) : Lattice d := fun i => ⌊x i⌋

theorem ae_noninteger_coordinates (d : ℕ) :
    ∀ᵐ x : Space d ∂volume, ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro z
  exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (z : ℝ)

theorem sub_floorLattice_mem_unitCube {d : ℕ} (x : Space d) :
    x - castLattice (floorLattice x) ∈ unitCube d := by
  apply mem_unitCube.mpr
  intro i
  change 0 ≤ x i - (⌊x i⌋ : ℝ) ∧ x i - (⌊x i⌋ : ℝ) ≤ 1
  have hl := Int.floor_le (x i)
  have hu := Int.lt_floor_add_one (x i)
  constructor <;> linarith

theorem floorLattice_eq_of_mem_unitVoxel {d : ℕ} {x : Space d}
    (hx : ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ)) {z : Lattice d}
    (hz : x - castLattice z ∈ unitCube d) : floorLattice x = z := by
  funext i
  apply Int.floor_eq_iff.mpr
  have hi := mem_unitCube.mp hz i
  change 0 ≤ x i - (z i : ℝ) ∧ x i - (z i : ℝ) ≤ 1 at hi
  constructor
  · linarith
  · have hne : x i ≠ (z i : ℝ) + 1 := by
      simpa using hx i (z i + 1)
    by_contra hn
    apply hne
    linarith

theorem Tiles.aeTiles_thickening {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Lattice d)} (h : Tiles F A) :
    AETiles (Thickening F) (castLattice '' A) := by
  apply (ae_noninteger_coordinates d).mono
  intro x hx
  obtain ⟨⟨f, a⟩, hfa⟩ := h.2 (floorLattice x)
  change (f : Lattice d) + (a : Lattice d) = floorLattice x at hfa
  refine ⟨⟨castLattice (a : Lattice d), ⟨(a : Lattice d), a.property, rfl⟩⟩, ?_, ?_⟩
  · refine ⟨(f : Lattice d), f.property, ?_⟩
    change x - castLattice (a : Lattice d) - castLattice (f : Lattice d) ∈ unitCube d
    have heq : x - castLattice (a : Lattice d) - castLattice (f : Lattice d) =
        x - castLattice (floorLattice x) := by
      rw [← hfa, map_add]
      abel
    rw [heq]
    exact sub_floorLattice_mem_unitCube x
  · intro b hb
    obtain ⟨b', hb', hb_eq⟩ := b.property
    obtain ⟨f', hf', hf'b⟩ := hb
    have hvoxel : x - castLattice (f' + b') ∈ unitCube d := by
      have heq : x - castLattice (f' + b') =
          x - (b : Space d) - castLattice f' := by
        rw [map_add, ← hb_eq]
        abel
      rw [heq]
      exact hf'b
    have hcorner := floorLattice_eq_of_mem_unitVoxel hx hvoxel
    have hp : ((⟨f', hf'⟩ : ↥F), (⟨b', hb'⟩ : A)) = (f, a) := by
      apply h.1
      change f' + b' = (f : Lattice d) + (a : Lattice d)
      exact hcorner.symm.trans hfa.symm
    apply Subtype.ext
    calc
      (b : Space d) = castLattice b' := hb_eq.symm
      _ = castLattice (a : Lattice d) :=
        congrArg castLattice (congrArg (fun p : ↥F × A => (p.2 : Lattice d)) hp)

end PeriodicTilingThree

end

end OAI
