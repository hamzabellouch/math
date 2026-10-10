import OAI.NumberTheory.Ostmann.Arithmetic.SignedSplitSupport
import OAI.NumberTheory.Ostmann.Arithmetic.SequentialProductSupport
import OAI.NumberTheory.Ostmann.Characters.TreeSplitCoordinates

namespace OAI

/-! # Fixed residue data at an exposed arithmetic split -/

namespace Ostmann

open scoped BigOperators Classical

/-- All entries are known before the child product is exposed. The units
contain the current giants and the nonbulk constants. -/
structure ArithmeticSplitData (Q : ℕ) where
  frequency : ℤ
  frequency_ne_zero : frequency ≠ 0
  frequency_dvd : frequency.natAbs ∣ Q
  leftFrequency : ℤ
  rightFrequency : ℤ
  leftFactor : (ZMod frequency.natAbs)ˣ
  rightFactor : (ZMod frequency.natAbs)ˣ
  parentProduct : (ZMod frequency.natAbs)ˣ

instance ArithmeticSplitData.modulusNeZero {Q : ℕ} (d : ArithmeticSplitData Q) :
    NeZero d.frequency.natAbs := ⟨Int.natAbs_ne_zero.mpr d.frequency_ne_zero⟩

def ArithmeticSplitData.reducedModulus {Q : ℕ} (d : ArithmeticSplitData Q) : ℕ :=
  reducedFrequency (d.leftFrequency.natAbs.gcd d.rightFrequency.natAbs) d.frequency.natAbs

def ArithmeticSplitData.test {Q : ℕ} (d : ArithmeticSplitData Q) (x : (ZMod Q)ˣ) : Prop :=
  (d.leftFrequency : ZMod d.frequency.natAbs) *
      (d.leftFactor * (d.parentProduct / ZMod.unitsMap d.frequency_dvd x) :
        (ZMod d.frequency.natAbs)ˣ) =
    (d.rightFrequency : ZMod d.frequency.natAbs) *
      (d.rightFactor * ZMod.unitsMap d.frequency_dvd x : (ZMod d.frequency.natAbs)ˣ)

theorem ArithmeticSplitData.pair_probability_le {Q : ℕ} [NeZero Q]
    (d e : ArithmeticSplitData Q) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ, if d.test x ∧ e.test x then (1 : ℝ) else 0) ≤
      2 * ((d.reducedModulus.lcm e.reducedModulus).divisors.card : ℝ) ^ 2 /
        d.reducedModulus.lcm e.reducedModulus := by
  have h := signed_joint_split_probability_le d.frequency_dvd e.frequency_dvd
    d.leftFrequency d.rightFrequency e.leftFrequency e.rightFrequency
    d.leftFactor d.rightFactor d.parentProduct e.leftFactor e.rightFactor e.parentProduct
  convert h using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [ArithmeticSplitData.test]
    split_ifs with ht
    · exact ite_eq_left ht
    · exact ite_eq_right ht
  · rfl

/-- `none` means a preceding unit or support test failed. It has zero
weight and does not impose any condition on an unexposed split. -/
def arithmeticPairSplitTest {Q : ℕ} (d : Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) : Prop :=
  match d with
  | none => False
  | some (d, e) => d.test x ∧ e.test x

theorem arithmeticPairSplit_probability_le {Q : ℕ} [NeZero Q]
    (d : Option (ArithmeticSplitData Q × ArithmeticSplitData Q)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ d₁ d₂, d = some (d₁, d₂) →
      2 * ((d₁.reducedModulus.lcm d₂.reducedModulus).divisors.card : ℝ) ^ 2 /
        d₁.reducedModulus.lcm d₂.reducedModulus ≤ B) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ, if arithmeticPairSplitTest d x then (1 : ℝ) else 0) ≤ B := by
  cases d with
  | none => simpa only [arithmeticPairSplitTest, ↓reduceIte, Finset.sum_const_zero, mul_zero] using hB
  | some d =>
      have h := (d.1.pair_probability_le d.2).trans (hbound d.1 d.2 rfl)
      convert h using 1
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [arithmeticPairSplitTest]
      split_ifs with ht
      · exact ite_eq_left ht
      · exact ite_eq_right ht

/-- All residue data are functions of the exposed prefix alone. This
derives the product bound for the actual two-history congruence tests. -/
theorem arithmetic_sequential_support_le {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hbound : ∀ past d e, data past = some (d, e) →
      2 * ((d.reducedModulus.lcm e.reducedModulus).divisors.card : ℝ) ^ 2 /
        d.reducedModulus.lcm e.reducedModulus ≤ B past.length)
    (n : ℕ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples (ZMod Q)ˣ n,
          sequentialSupport (fun past y => arithmeticPairSplitTest (data past) y) [] n x) ≤
      ∏ j ∈ Finset.range n, B j := by
  have h := sequentialSupport_average_le_product
    (fun past y => arithmeticPairSplitTest (data past) y) B hB
    (fun past => arithmeticPairSplit_probability_le (data past) (B past.length) (hB _)
      (hbound past)) [] n
  simpa only [List.length_nil, Nat.zero_add] using h

end Ostmann

end OAI
