import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram
import OAI.Combinatorics.ContingencyTables.Transport.FiniteScaledDraw

namespace OAI

/-! # Polynomial binary execution of the bounded quotient draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def scaledWordValue (x : ℕ×List Bool) : ℕ :=
  x.1*StackAddition.value x.2/2^x.2.length

def scaledWordRealizer : Realizer scaledWordValue :=
  (composition (pair
    (composition (pair first (composition second bitValue)) multiply)
    (composition second bitDenominatorRealizer)) quotient).congr (by
      intro x
      simp only [Function.comp_apply,bitDenominator_eq,scaledWordValue])

theorem polynomial_scaledWord : PolynomialTime scaledWordRealizer := by
  unfold scaledWordRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_bitValue)) polynomial_multiply)
    (polynomial_composition polynomial_second polynomial_bitDenominator)) polynomial_quotient)

theorem scaledWordValue_ofFn (M k : ℕ) (hM : 0<M) (bits : Fin k → Bool) :
    scaledWordValue (M,List.ofFn bits)=(FairBits.scaledBitInteger M k hM bits).val := by
  simp only [scaledWordValue,List.length_ofFn,bitValue_eq_word]
  rfl

/-- Every finite input yields the prescribed bounded integer. -/
theorem scaledWordValue_lt (M : ℕ) (hM : 0<M) (bits : List Bool) :
    scaledWordValue (M,bits)<M := by
  let w : Fin bits.length → Bool := fun i => bits[i]
  have he : List.ofFn w=bits := List.ofFn_getElem
  rw [←he,scaledWordValue_ofFn M bits.length hM w]
  exact (FairBits.scaledBitInteger M bits.length hM w).isLt

end ContingencyTables.ProfilePrograms

end OAI
