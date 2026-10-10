import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityBits
import OAI.Combinatorics.ContingencyTables.Machines.ScaledWordProgram

namespace OAI

/-! # Polynomial binary arithmetic for sequential subset inclusion

The rational inclusion threshold is computed by an integer product and
quotient. In particular the denominator is never expanded into a
unary loop; the only exponential integer has the supplied word length
as its binary length.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

abbrev HeadInput := (ℕ×ℕ)×List Bool

def includeCode (z : HeadInput) : Bool :=
  decide (StackAddition.value z.2<2^z.2.length*min z.1.2 z.1.1/z.1.1)

def includeRealizer : Realizer includeCode := by
  let N : Realizer (fun z : HeadInput => z.1.1) := composition first first
  let K : Realizer (fun z : HeadInput => z.1.2) := composition first second
  let M := composition (pair K N) minimum
  let D : Realizer (fun z : HeadInput => TreeTyped.bitDenominator z.2) :=
    composition second bitDenominatorRealizer
  let T := composition (pair (composition (pair D M) multiply) N) quotient
  exact (composition (pair (composition second bitValue) T) less).congr (by
    intro z
    simp only [Function.comp_apply,bitDenominator_eq,includeCode])

theorem polynomial_include : PolynomialTime includeRealizer := by
  unfold includeRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_bitValue)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_bitDenominator)
        (polynomial_composition (polynomial_pair
          (polynomial_composition polynomial_first polynomial_second)
          (polynomial_composition polynomial_first polynomial_first)) polynomial_minimum))
        polynomial_multiply)
      (polynomial_composition polynomial_first polynomial_first)) polynomial_quotient))
    polynomial_less)

noncomputable section

theorem inclusion_threshold (B n k : ℕ) :
    FairBits.rationalThreshold B (FixedCardinalityLaw.headProbability n k)=
      2^B*min k (n+1)/(n+1) := by
  let M := 2^B*min k (n+1)
  have hd : ((n+1:ℕ):ℚ)≠0 := by positivity
  have he : (2:ℚ)^B*FixedCardinalityLaw.headProbability n k=
      (M:ℚ)/(n+1:ℕ) := by
    simp only [FixedCardinalityLaw.headProbability,M,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_add,Nat.cast_one]
    ring
  change ⌊(2:ℚ)^B*FixedCardinalityLaw.headProbability n k⌋₊=_
  rw [he]
  have hh := Nat.mul_cast_floor_div_cancel (R := ℚ) (n := n+1) (by omega)
    ((M:ℚ)/(n+1:ℕ))
  simpa only [div_mul_cancel₀ _ hd,Nat.floor_natCast] using hh.symm

/-- The executable natural-number comparison is exactly the inclusion
decision in the finite Boolean law. -/
theorem includeCode_ofFn (B n k : ℕ) (bits : Fin B → Bool) :
    includeCode ((n+1,k),List.ofFn bits)=FixedCardinalityBits.headDraw B n k bits := by
  simp only [includeCode,List.length_ofFn,bitValue_eq_word,FixedCardinalityBits.headDraw,
    FairBits.rationalThresholdAccept,inclusion_threshold]

end
end ContingencyTables.FixedCardinalityProgram

end OAI
