import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts

namespace OAI

/-! # Binary execution of the rational acceptance coin

The integer quotient computes the exact floor threshold used by the
finite-word acceptance law. The word length controls all powering and
word traversal, even for malformed fraction inputs.
-/

namespace ContingencyTables.FractionAcceptanceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

abbrev Input := TreeFraction.Fraction×List Bool

def scaledNumerator (z : Input) : ℕ := z.1.1*bitDenominator z.2

def scaledNumeratorRealizer : Realizer scaledNumerator :=
  composition (f := fun z : Input => (z.1.1,bitDenominator z.2))
    (g := fun x : ℕ×ℕ => x.1*x.2)
    (pair (composition first first) (composition second bitDenominatorRealizer)) multiply

lemma polynomial_scaledNumerator : PolynomialTime scaledNumeratorRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_second polynomial_bitDenominator)) polynomial_multiply

def threshold (z : Input) : ℕ := scaledNumerator z/z.1.2

def thresholdRealizer : Realizer threshold :=
  composition (f := fun z : Input => (scaledNumerator z,z.1.2))
    (g := fun x : ℕ×ℕ => x.1/x.2)
    (pair scaledNumeratorRealizer (composition first second)) quotient

lemma polynomial_threshold : PolynomialTime thresholdRealizer :=
  polynomial_composition (polynomial_pair polynomial_scaledNumerator
    (polynomial_composition polynomial_first polynomial_second)) polynomial_quotient

def acceptCode (z : Input) : Bool := decide (StackAddition.value z.2<threshold z)

def acceptCodeRealizer : Realizer acceptCode :=
  composition (f := fun z : Input => (StackAddition.value z.2,threshold z))
    (g := fun x : ℕ×ℕ => decide (x.1<x.2))
    (pair (composition second bitValue) thresholdRealizer) less

theorem polynomial_acceptCode : PolynomialTime acceptCodeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_bitValue)
    polynomial_threshold) polynomial_less

noncomputable section

lemma fraction_threshold (B : ℕ) (q : TreeFraction.Fraction) :
    FairBits.rationalThreshold B (TreeFraction.val q)=q.1*2^B/q.2 := by
  by_cases hd : q.2=0
  · simp [FairBits.rationalThreshold,TreeFraction.val,hd]
  · let M := q.1*2^B
    have hdq : (q.2:ℚ)≠0 := by exact_mod_cast hd
    have he : (2:ℚ)^B*TreeFraction.val q=(M:ℚ)/q.2 := by
      simp only [TreeFraction.val,M,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    change ⌊(2:ℚ)^B*TreeFraction.val q⌋₊=_
    rw [he]
    have hh := Nat.mul_cast_floor_div_cancel (R := ℚ) (n := q.2)
      hd ((M:ℚ)/q.2)
    simpa only [div_mul_cancel₀ _ hdq,Nat.floor_natCast] using hh.symm

/-- The compiled decision agrees on every Boolean word with the
rational threshold used in the proved companion transition law. -/
theorem acceptCode_ofFn (q : TreeFraction.Fraction) (B : ℕ) (bits : Fin B → Bool) :
    acceptCode (q,List.ofFn bits)=decide (FairBits.rationalThresholdAccept B (TreeFraction.val q) bits) := by
  simp only [acceptCode,threshold,scaledNumerator,bitDenominator_eq,List.length_ofFn,
    bitValue_eq_word,FairBits.rationalThresholdAccept,fraction_threshold]

end
end ContingencyTables.FractionAcceptanceProgram

end OAI
