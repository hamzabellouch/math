import OAI.Combinatorics.ContingencyTables.Dense.DenseNormalizeSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyTableComplexity

namespace OAI

/-! # Dense sampling from margins with a computed grid and fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

abbrev CanonicalParameters := (List ℕ×List ℕ)×(ℕ×ℕ)
abbrev CanonicalDrawData := CanonicalParameters×List Bool

def zeroGrid (z : List ℕ×List ℕ) : List ℕ :=
  (cellPairs (z.1.tail,z.2.tail)).map (fun _ => 0)

def zeroGridRealizer : Realizer zeroGrid :=
  composition (composition (pair (composition first tail) (composition second tail))
    cellPairsRealizer) (map (constant 0))

theorem polynomial_zeroGrid : PolynomialTime zeroGridRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_tail)
      (polynomial_composition polynomial_second polynomial_tail)) polynomial_cellPairs)
    (polynomial_map (polynomial_constant 0))

def canonicalInput (z : CanonicalDrawData) : DenseDrawData :=
  (((((z.1.1,zeroGrid z.1.1),z.1.2.1),z.1.2.2),
    GreedyFeasibleTable.listMatrix z.1.1.1 z.1.1.2),z.2)

def canonicalInputRealizer : Realizer canonicalInput := by
  let margins : Realizer (fun z : CanonicalDrawData => z.1.1) := composition first first
  let parameters : Realizer (fun z : CanonicalDrawData => z.1.2) := composition first second
  let grid := composition margins zeroGridRealizer
  let fallback := composition margins GreedyFeasibleTable.tableRealizer
  exact pair (pair (pair (pair (pair margins grid) (composition parameters first))
    (composition parameters second)) fallback) second

theorem polynomial_canonicalInput : PolynomialTime canonicalInputRealizer := by
  have hm : PolynomialTime (composition
      (first (A := CanonicalParameters) (B := List Bool)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hp : PolynomialTime (composition
      (first (A := CanonicalParameters) (B := List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  unfold canonicalInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_pair (polynomial_pair hm (polynomial_composition hm polynomial_zeroGrid))
      (polynomial_composition hp polynomial_first))
    (polynomial_composition hp polynomial_second))
    (polynomial_composition hm GreedyFeasibleTable.polynomial_table)) polynomial_second

def canonicalDenseDraw (z : CanonicalDrawData) : MatrixCode :=
  normalizedDenseCode (canonicalInput z)

def canonicalDenseDrawRealizer : Realizer canonicalDenseDraw :=
  composition canonicalInputRealizer normalizedDenseCodeRealizer

theorem polynomial_canonicalDenseDraw : PolynomialTime canonicalDenseDrawRealizer :=
  polynomial_composition polynomial_canonicalInput polynomial_normalizedDenseCode

end ContingencyTables.DensePrograms

end OAI
