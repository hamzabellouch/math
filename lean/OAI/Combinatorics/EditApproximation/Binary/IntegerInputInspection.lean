import OAI.Combinatorics.EditApproximation.Binary.IntegerOccurrenceIndex
import OAI.Combinatorics.EditApproximation.Probability.ExactSuffixDPWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Explicit linear scans select the input-dependent symbol and position
widths. The alphabet exponent is used only in the analysis. -/

namespace EditApproximation



 theorem integerMagnitudeWithWork_spec (symbols : List ℤ) :
    integerMagnitudeWithWork symbols = (integerMagnitude symbols, 2 * symbols.length) := by
  induction symbols with
  | nil => rfl
  | cons z rest ih =>
    simp only [integerMagnitudeWithWork, ih, integerMagnitude, List.length_cons]
    congr 1

 theorem integerMagnitude_append (source target : List ℤ) :
    integerMagnitude (source ++ target) = max (integerMagnitude source) (integerMagnitude target) := by
  induction source with
  | nil => simp only [List.nil_append, integerMagnitude, Nat.zero_max]
  | cons z rest ih => simp only [List.cons_append, integerMagnitude, ih, max_assoc]

/-- Count the shifts in a literal binary-length loop. -/


private theorem size_div_two (n : ℕ) (hn : n ≠ 0) : n.size = (n / 2).size + 1 := by
  have hb : Nat.bit n.bodd n.div2 ≠ 0 := by rwa [Nat.bit_bodd_div2]
  have hs := Nat.size_bit hb
  rw [Nat.bit_bodd_div2] at hs
  simpa only [Nat.div2_val, Nat.succ_eq_add_one] using hs

 theorem inputBitLengthWithWork_spec (n : ℕ) :
    inputBitLengthWithWork n = (n.size, 2 * n.size + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [inputBitLengthWithWork]
    split_ifs with hn
    · subst n
      rfl
    · rw [ih (n / 2) (Nat.div_lt_self (by omega) (by decide)), size_div_two n hn]
      congr 1



 theorem integerInputInspectionWithWork_spec (source target : List ℤ) :
    (integerInputInspectionWithWork source target).1 =
      (integerInputSymbolBits source target, integerInputPositionBits target) := by
  simp only [integerInputInspectionWithWork, integerMagnitudeWithWork_spec,
    dpLength_spec, inputBitLengthWithWork_spec, integerInputSymbolBits,
    integerInputPositionBits, integerMagnitude_append]

 theorem integerInputInspectionWithWork_cost (source target : List ℤ) :
    (integerInputInspectionWithWork source target).2 ≤
      4 * (source.length + target.length) + 2 * integerInputSymbolBits source target +
        2 * integerInputPositionBits target + 8 := by
  simp only [integerInputInspectionWithWork, integerMagnitudeWithWork_spec,
    dpLength_spec, inputBitLengthWithWork_spec, integerInputSymbolBits,
    integerInputPositionBits, integerMagnitude_append]
  omega

end EditApproximation

end OAI
