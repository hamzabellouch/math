import Mathlib

namespace OAI

noncomputable section

universe u

namespace PeriodicTilingThree

abbrev Lattice (d : ℕ) := Fin d → ℤ

variable {G : Type u} [AddCommGroup G]

def Tiles (F : Finset G) (A : Set G) : Prop :=
  Function.Bijective (fun p : ↥F × A => (p.1 : G) + (p.2 : G))

def Period (A : Set G) (v : G) : Prop :=
  ∀ x : G, x + v ∈ A ↔ x ∈ A

def FullyPeriodic (A : Set G) : Prop :=
  ∃ P : AddSubgroup G, P.FiniteIndex ∧ ∀ v ∈ P, Period A v

open MeasureTheory

abbrev Space (d : ℕ) := Fin d → ℝ

def castLattice {d : ℕ} : Lattice d →+ Space d where
  toFun z i := (z i : ℝ)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

def unitCube (d : ℕ) : Set (Space d) := Set.Icc 0 1

def Thickening {d : ℕ} (F : Finset (Lattice d)) : Set (Space d) :=
  {x | ∃ z ∈ F, x - castLattice z ∈ unitCube d}

def AETiles {d : ℕ} (Ω A : Set (Space d)) : Prop :=
  ∀ᵐ x ∂volume, ∃! a : A, x - (a : Space d) ∈ Ω

def latticeOfBasis {d : ℕ} (b : Module.Basis (Fin d) ℝ (Space d)) :
    AddSubgroup (Space d) := (Submodule.span ℤ (Set.range b)).toAddSubgroup

def EuclideanFullyPeriodic {d : ℕ} (A : Set (Space d)) : Prop :=
  ∃ b : Module.Basis (Fin d) ℝ (Space d), ∀ v ∈ latticeOfBasis b, Period A v

def HasTileWithoutPeriodicComplement (d : ℕ) : Prop :=
  ∃ T : Finset (Lattice d), T.Nonempty ∧
    (∃ A : Set (Lattice d), Tiles T A) ∧
    ∀ A : Set (Lattice d), Tiles T A → ¬ FullyPeriodic A

theorem periodic_tiling_counterexample_and_minimality :
    (∃ T : Finset (Lattice 3), T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3),
        AETiles (Thickening T) A → ¬ EuclideanFullyPeriodic A)) ∧
    IsLeast {d : ℕ | HasTileWithoutPeriodicComplement d} 3 := by
  sorry

end PeriodicTilingThree

end

end OAI
