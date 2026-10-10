import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram
import OAI.Combinatorics.ContingencyTables.Transport.DyadicAcceptance

namespace OAI

/-! # Polynomial binary evaluation of the finite Metropolis coin -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

def dyadicWordAccept (z : List Bool×ℕ) : Bool :=
  decide (StackAddition.value z.1<2^(z.1.length-z.2))

/-- The power of two is built from a prefix of the supplied word. Thus
no binary integer supplied as a gap can cause an unbounded expansion. -/
def dyadicWordAcceptRealizer : Realizer dyadicWordAccept := by
  let N : Realizer (fun z : List Bool×ℕ => z.1.length-z.2) :=
    composition (pair (composition first listLength) second) subtract
  let B := composition (composition (pair first N) takeFast) bitDenominatorRealizer
  exact (composition (pair (composition first bitValue) B) less).congr (by
    intro z
    simp only [Function.comp_apply,bitDenominator_eq,List.length_take,dyadicWordAccept]
    rw [min_eq_left (Nat.sub_le _ _)])

theorem polynomial_dyadicWordAccept : PolynomialTime dyadicWordAcceptRealizer := by
  have hn : PolynomialTime (composition
      (pair (composition (first (A := List Bool) (B := ℕ)) listLength) second) subtract) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listLength) polynomial_second)
      polynomial_subtract
  have hb := polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first hn) polynomial_takeFast) polynomial_bitDenominator
  unfold dyadicWordAcceptRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_bitValue) hb) polynomial_less)

theorem dyadicWordAccept_ofFn (gap k : ℕ) (bits : Fin k → Bool) :
    dyadicWordAccept (List.ofFn bits,gap)=
      decide (FairBits.acceptDyadic gap k (FairBits.binaryWordEquiv k bits)) := by
  simp only [dyadicWordAccept,List.length_ofFn,bitValue_eq_word,FairBits.acceptDyadic]

end ContingencyTables.DensePrograms

end OAI
