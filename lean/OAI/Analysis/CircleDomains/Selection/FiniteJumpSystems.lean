import OAI.Analysis.CircleDomains.Selection.IncreasingChainRelations
import OAI.Analysis.CircleDomains.Selection.JumpChainEdges

namespace OAI

/-! Finite jump systems and their successive extensions. The label type is
retained, so adjoining a level preserves every previously installed edge. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

structure FiniteJumpSystem (X : Type*) where
  Label : Type
  finite : Fintype Label
  region : Label → Set X
  toll : Label → ℝ≥0∞

namespace FiniteJumpSystem

variable {X : Type*}

def empty : FiniteJumpSystem X :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim⟩

def append (A : FiniteJumpSystem X) (n : ℕ) (V : Fin n → Set X)
    (T : Fin n → ℝ≥0∞) : FiniteJumpSystem X := by
  letI := A.finite
  exact ⟨A.Label ⊕ Fin n, inferInstance, Sum.elim A.region V, Sum.elim A.toll T⟩

variable {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def edge (A : FiniteJumpSystem X) (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) : X → X → ℝ≥0∞ → Prop :=
  physicalJumpEdge d ν N g m A.region A.toll

theorem edge_append_old (A : FiniteJumpSystem X) (n : ℕ) (V : Fin n → Set X)
    (T : Fin n → ℝ≥0∞) (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) {x y : X} {a : ℝ≥0∞}
    (h : A.edge d ν N g m x y a) : (A.append n V T).edge d ν N g m x y a := by
  rcases h with h | ⟨i, hx, hy, ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨Sum.inl i, hx, hy, ha⟩

theorem edge_append_new (A : FiniteJumpSystem X) (n : ℕ) (V : Fin n → Set X)
    (T : Fin n → ℝ≥0∞) (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (i : Fin n) {x y : X}
    (hx : x ∈ V i ∩ d.quotientDomain) (hy : y ∈ V i ∩ d.quotientDomain) :
    (A.append n V T).edge d ν N g m x y (T i) :=
  Or.inr ⟨Sum.inr i, hx, hy, rfl⟩

end FiniteJumpSystem

end CircleDomainRigidity

end

end OAI
