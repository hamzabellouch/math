import OAI.Combinatorics.EditApproximation.Queries.QueryBoundedBody

namespace OAI

namespace EditApproximation.BitQuery

/-- A failed domain test supplies the same zero word to the adaptive continuation. -/
def restrictedOracle {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (oracle : {key // P key} → BinaryFraction) (key : ι) : BinaryFraction :=
  if h : (test key).1 = true then oracle ⟨key, (htest key).mp h⟩ else BinaryFraction.nat 0

def restrictedReadWork {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (readWork : {key // P key} → ℕ) (key : ι) : ℕ :=
  (test key).2 + if h : (test key).1 = true then readWork ⟨key, (htest key).mp h⟩ else 0

theorem restrictWithWork_work {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (program : BitQuery ι BinaryFraction) (oracle : {key // P key} → BinaryFraction)
    (readWork : {key // P key} → ℕ) :
    (restrictWithWork P test htest program).work oracle readWork =
      program.work (restrictedOracle P test htest oracle) (restrictedReadWork P test htest readWork) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact congrArg (steps + ·) ih
  | read key next ih =>
    by_cases h : (test key).1 = true
    · simp only [restrictWithWork, h, dite_true, work, restrictedOracle, restrictedReadWork, ih,
        Nat.add_assoc]
    · simp only [restrictWithWork, h, Bool.false_eq_true, dite_false, work, restrictedOracle, restrictedReadWork, ih,
        Nat.add_zero]

theorem restrictWithWork_value {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (program : BitQuery ι BinaryFraction) (oracle : {key // P key} → BinaryFraction) :
    (restrictWithWork P test htest program).value oracle =
      program.value (restrictedOracle P test htest oracle) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact ih
  | read key next ih =>
    by_cases h : (test key).1 = true
    · simp only [restrictWithWork, h, dite_true, value, restrictedOracle, ih]
    · simp only [restrictWithWork, h, Bool.false_eq_true, dite_false, value, restrictedOracle, ih]

theorem restrictedOracle_width {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (oracle : {key // P key} → BinaryFraction) (B : ℕ) (hB : 2 ≤ B)
    (hw : ∀ key, (oracle key).width ≤ B) (key : ι) :
    (restrictedOracle P test htest oracle key).width ≤ B := by
  unfold restrictedOracle
  split
  · exact hw _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hB)

end EditApproximation.BitQuery

namespace EditApproximation

theorem queryPhysicalBoundedWithWork_cost {M J n : ℕ} (passes copies T S B : ℕ)
    (request : PhysicalTableRequest M J n)
    (hp : Nat.size passes ≤ B) (hc : Nat.size copies ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrp : Nat.size request.pass ≤ B) (hrc : Nat.size request.copy ≤ B)
    (hri : Nat.size request.index ≤ B) :
    (queryPhysicalBoundedWithWork passes copies T S request).2 ≤ 50 * B + 20 := by
  have hpass := binaryNaturalCompareWithWork_cost request.pass passes
  have hcopy := binaryNaturalCompareWithWork_cost request.copy copies
  have hcap := binaryNaturalAddWithWork_cost T S
  have hlen := bitAddWithWork_length T.bits S.bits false
  have hlen' : (binaryNaturalAddWithWork T S).1.length ≤ B + 1 := by
    change (bitAddWithWork T.bits S.bits false).1.length ≤ _
    apply hlen.trans
    simpa only [Nat.size_eq_bits_len] using Nat.add_le_add_right (max_le hT hS) 1
  have hindex := wordLEWithWork_cost request.index.bits (binaryNaturalAddWithWork T S).1
  rw [Nat.size_eq_bits_len] at hindex
  change (binaryNaturalCompareWithWork request.pass passes).2 +
    (binaryNaturalCompareWithWork request.copy copies).2 + (binaryNaturalAddWithWork T S).2 +
    (wordLEWithWork request.index.bits (binaryNaturalAddWithWork T S).1).2 + 4 ≤ _
  omega

end EditApproximation

end OAI
