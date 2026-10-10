import OAI.Combinatorics.ContingencyTables.Dense.DenseExponentArithmetic
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPreparedProposal

namespace OAI

/-! # Binary execution of one dense exponent component -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms

abbrev ComponentData := (ℕ×ℕ)×(ℕ×ℕ)

def eighthPower : Realizer (fun n : ℕ => n^8) :=
  (composition fourthPower squareNat).congr (by
    intro n
    simp only [Function.comp_apply]
    ring)

lemma polynomial_eighthPower : PolynomialTime eighthPower :=
  polynomial_congr _ (polynomial_composition polynomial_fourthPower polynomial_squareNat)

def componentValue (z : ComponentData) : ℕ :=
  GridBoundary.componentExponent z.1.1 z.1.2 z.2.1 z.2.2

def componentRealizer : Realizer componentValue := by
  let D : Realizer (fun z : ComponentData => z.1.1) := composition first first
  let S : Realizer (fun z : ComponentData => z.1.2) := composition first second
  let P : Realizer (fun z : ComponentData => z.2.1) := composition second first
  let N : Realizer (fun z : ComponentData => z.2.2) := composition second second
  let D4 := composition D fourthPower
  let D8 := composition D eighthPower
  let pos := composition (pair D4
    (composition (pair (composition (pair D8 P) multiply)
      (composition (pair D S) multiply)) add)) multiply
  let neg := composition (pair (composition (pair D4 D8) multiply) N) multiply
  let den := composition (pair S D8) multiply
  exact (composition (pair (composition (pair neg pos) subtract) den) quotient).congr
    (by intro z; rfl)

/-- Cost is polynomial in the binary data, even when the represented
margin values and the quotient are large. -/
theorem polynomial_component : PolynomialTime componentRealizer := by
  have hD : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := ℕ×ℕ)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hS : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hP : PolynomialTime (composition
      (second (A := ℕ×ℕ) (B := ℕ×ℕ)) first) :=
    polynomial_composition polynomial_second polynomial_first
  have hN : PolynomialTime (composition
      (second (A := ℕ×ℕ) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_second polynomial_second
  have h4 := polynomial_composition hD polynomial_fourthPower
  have h8 := polynomial_composition hD polynomial_eighthPower
  have hp := polynomial_composition (polynomial_pair h4
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair h8 hP) polynomial_multiply)
      (polynomial_composition (polynomial_pair hD hS) polynomial_multiply)) polynomial_add))
    polynomial_multiply
  have hn := polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair h4 h8) polynomial_multiply) hN) polynomial_multiply
  have hd := polynomial_composition (polynomial_pair hS h8) polynomial_multiply
  unfold componentRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair hn hp) polynomial_subtract) hd) polynomial_quotient)

theorem componentValue_eq_floor (d s positive negative : ℕ) :
    componentValue ((d,s),(positive,negative))=
      ⌊(d : ℚ)^4*(-((positive : ℚ)-negative)/s-(d : ℚ)/(d : ℚ)^8)⌋₊ :=
  GridBoundary.componentExponent_eq d s positive negative

end ContingencyTables.DensePrograms

end OAI
