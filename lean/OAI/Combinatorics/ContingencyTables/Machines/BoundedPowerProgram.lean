import OAI.Combinatorics.ContingencyTables.Machines.BinaryPowerProgram

namespace OAI

/-! # Reusing a unary allowance across a binary transition table -/

namespace ContingencyTables.BoundedPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def powerInput (z : List Bool×ℕ) : ℕ×ℕ := (2,z.1.length-z.2)

def powerInputRealizer : Realizer powerInput :=
  pair (constant 2) (composition (pair (composition first listLength) second) subtract)

lemma polynomial_powerInput : PolynomialTime powerInputRealizer :=
  polynomial_pair (polynomial_constant 2) (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_listLength) polynomial_second)
    polynomial_subtract)

def power (z : List Bool×ℕ) : ℕ := BinaryPowerPrograms.power (powerInput z)

def powerRealizer : Realizer power :=
  composition powerInputRealizer BinaryPowerPrograms.powerRealizer

/-- A single allowance list can be shared by all entries in the finite
matrix. Each binary power then has polynomial cost in the supplied data. -/
theorem polynomial_power : PolynomialTime powerRealizer := by
  apply work_composition polynomial_powerInput BinaryPowerPrograms.work_power (Polynomial.X+9)
  intro z
  have hl: z.1.length ≤ weight z := (list_length_le_weight z.1).trans (weight_fst z)
  have hw : weight (2:ℕ)≤9 := by decide
  simp only [powerInput,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

theorem power_eq (xs : List Bool) (gap : ℕ) : power (xs,gap)=2^(xs.length-gap) :=
  BinaryPowerPrograms.power_eq 2 (xs.length-gap)

end ContingencyTables.BoundedPowerPrograms

end OAI
