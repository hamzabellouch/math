import Mathlib.LinearAlgebra.Projectivization.Cardinality
import OAI.Computability.UniqueGames.Quadratic.Block

namespace OAI

section

/-! Exact field-line count for the quadratic block's erasure probability. -/

namespace UniqueGamesTheorem.Quadratic

/-- Actual one-dimensional field directions, with proportional nonzero
vectors identified. -/
abbrev FieldLine (F : Type*) [Field F] := Projectivization F (Vec F)

variable {F : Type*} [Field F]

/-- A chosen nonzero generator, only used with generator-independent data. -/
noncomputable def lineGenerator (A : FieldLine F) : Vec F := A.rep

theorem lineGenerator_ne_zero (A : FieldLine F) : lineGenerator A ≠ 0 :=
  A.rep_nonzero

theorem line_lineGenerator (A : FieldLine F) : line (lineGenerator A) = A.submodule :=
  A.submodule_eq.symm

theorem fieldLine_finrank (A : FieldLine F) : Module.finrank F A.submodule = 1 :=
  A.finrank_submodule

variable [Finite F]

/-- The denominator of the block erasure probability is exactly `q²+q+1`. -/
theorem card_FieldLine : Nat.card (FieldLine F) = Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := Projectivization.card_of_finrank F (Vec F) (n := 3)
    (Module.finrank_fin_fun (R := F))
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using h

/-- The same count on one-dimensional submodules, rather than representatives. -/
theorem card_fieldLine_submodules :
    Nat.card {A : Submodule F (Vec F) // Module.finrank F A = 1} =
      Nat.card F ^ 2 + Nat.card F + 1 := by
  rw [← Nat.card_congr (Projectivization.equivSubmodule F (Vec F))]
  exact card_FieldLine

theorem card_FieldLine_pos : 0 < Nat.card (FieldLine F) := by
  rw [card_FieldLine]
  exact Nat.succ_pos _

/-- Written over rationals, as needed for the finite rational noise law. -/
theorem reciprocal_card_FieldLine :
    (Nat.card (FieldLine F) : ℚ)⁻¹ =
      ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ := by
  rw [card_FieldLine]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]

end UniqueGamesTheorem.Quadratic

end

end OAI
