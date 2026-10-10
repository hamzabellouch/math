import OAI.Combinatorics.ExpectationThreshold.Basic
import OAI.Combinatorics.ExpectationThreshold.ProbabilityColors
import OAI.Combinatorics.ExpectationThreshold.SelectorTruncationDefinitions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI

/-!
# Actual moves and profiles for the simultaneous selector

We retain all colorings of minimum total movement for at least one original
family member. This avoids an arbitrary tie-breaking order; each retained
coloring still has the member-specific minimality used in reconstruction.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A probability mass for each actual member of the family. -/
structure MassFamily (F : Family α) where
  weight : ↥F → α → ℝ
  nonneg : ∀ H x, 0 ≤ weight H x
  total : ∀ H, ∑ x, weight H x = 1
  supported : ∀ H x, x ∉ H.val → weight H x = 0

/-- Colors have zero-based indices; the actual color level is one larger. -/
def prefixSet {s : ℕ} (z : Coloring α s) (i : Fin s) : Finset α :=
  Finset.univ.filter fun x => (z x).val ≤ i.val

def dscale {s : ℕ} (i : Fin s) : ℝ := ((2 : ℝ) ^ (i.val + 1))⁻¹

/-- `Earlier a z` means that the move from `a` to `z` only lowers colors. -/
def Earlier {s : ℕ} (a z : Coloring α s) : Prop := ∀ x, z x ≤ a x

def changes {s : ℕ} (a z : Coloring α s) : Finset α :=
  Finset.univ.filter fun x => z x < a x

def crossings {s : ℕ} (a z : Coloring α s) (i : Fin s) : ℕ :=
  (prefixSet z i \ prefixSet a i).card

def movement {s : ℕ} (a z : Coloring α s) : ℕ :=
  ∑ x, ((a x).val - (z x).val)

def movedRow {s : ℕ} (a z : Coloring α s) (i : Fin s) : Finset α :=
  Finset.univ.filter fun x => (z x).val = i.val ∧ (z x).val < (a x).val

/-- The full profile retains both final and original colors. -/
abbrev Profile (s : ℕ) := Fin s → Color s → ℕ

def profile {s : ℕ} (a z : Coloring α s) : Profile s :=
  fun i h => (Finset.univ.filter fun x =>
    (z x).val = i.val ∧ a x = h ∧ i.val < h.val).card

def rowCount {s : ℕ} (n : Profile s) (i : Fin s) : ℕ := ∑ h, n i h

def profileSize {s : ℕ} (n : Profile s) : ℕ := ∑ i, rowCount n i

def profileCrossings {s : ℕ} (n : Profile s) (i : Fin s) : ℕ :=
  ∑ j : Fin s, ∑ h : Color s,
    if j.val ≤ i.val ∧ i.val < h.val then n j h else 0

def FeasibleFor {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) (H : ↥F) : Prop :=
  ∀ i : Fin s, ∃ ε : ℝ,
    Admissible (mu.weight H) (prefixSet z i) (crossings a z i : ℝ) (dscale i) ε

def Feasible {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) : Prop :=
  Earlier a z ∧ ∃ H : ↥F, FeasibleFor mu a z H

def BoundedFeasible {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) (H₀ : ↥F) (z : Coloring α s) : Prop :=
  Feasible mu a z ∧ changes a z ⊆ H₀.val

def IsMinimalMove {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) (H₀ : ↥F) (z : Coloring α s) : Prop :=
  BoundedFeasible mu a H₀ z ∧
    ∀ w, BoundedFeasible mu a H₀ w → movement a z ≤ movement a w

def Selected {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) : Prop := ∃ H₀ : ↥F, IsMinimalMove mu a H₀ z

def selectedMoves {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) : Finset (Coloring α s) := by
  classical
  exact Finset.univ.filter (Selected mu a)

/-- An actual bad original coloring, its selected endpoint, and its full profile. -/
def Captured {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) : Prop :=
  ∃ H : ↥F, ∀ i : Fin s,
    1 - dscale i ≤ ∑ x ∈ prefixSet a i, mu.weight H x

def Bad {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) : Prop := ¬ Captured mu a

def groupOriginals {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s) : Finset (Coloring α s) := by
  classical
  exact Finset.univ.filter fun a => Bad mu a ∧ Selected mu a z ∧ profile a z = n

def meanColor {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s) : ℝ :=
  ∑ x, ((a x).val + 1 : ℝ) * mu.weight H x

end TalagrandThreshold.Selector

end

end OAI
