import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredStoredRecords

namespace OAI

/-! # Prefix filtering by executed bounded-list membership tests -/

namespace LowSpaceSubsetSum
namespace IndexedMask

variable {n : ℕ}

def compatibleAcc (ones zeros domain selected : IndexedMask n) : List (Fin n) → Bool × ℕ
  | [] => (true, 1)
  | i :: xs =>
    let o := CountedWeights.member i ones.indices
    let z := CountedWeights.member i zeros.indices
    let d := CountedWeights.member i domain.indices
    let s := CountedWeights.member i selected.indices
    let r := compatibleAcc ones zeros domain selected xs
    (((!(o.1 && d.1) || s.1) && !(z.1 && s.1)) && r.1,
      o.2 + z.2 + d.2 + s.2 + r.2 + 8)

theorem compatibleAcc_value (ones zeros domain selected : IndexedMask n) (xs : List (Fin n)) :
    (compatibleAcc ones zeros domain selected xs).1 = true ↔
      ∀ i ∈ xs, (i ∈ ones.indices ∧ i ∈ domain.indices → i ∈ selected.indices) ∧
        ¬(i ∈ zeros.indices ∧ i ∈ selected.indices) := by
  induction xs with
  | nil => simp [compatibleAcc]
  | cons i xs ih =>
    by_cases ho : i ∈ ones.indices <;> by_cases hz : i ∈ zeros.indices <;>
      by_cases hd : i ∈ domain.indices <;> by_cases hs : i ∈ selected.indices <;>
      simp [compatibleAcc, CountedWeights.member_value, ho, hz, hd, hs, ih]

theorem compatibleAcc_work (ones zeros domain selected : IndexedMask n) (xs : List (Fin n)) :
    (compatibleAcc ones zeros domain selected xs).2 ≤ (4 * n + 12) * xs.length + 1 := by
  induction xs with
  | nil => simp [compatibleAcc]
  | cons i xs ih =>
    have ho := CountedWeights.member_work i ones.indices
    have hz := CountedWeights.member_work i zeros.indices
    have hd := CountedWeights.member_work i domain.indices
    have hs := CountedWeights.member_work i selected.indices
    have h₁ := ones.length_le
    have h₂ := zeros.length_le
    have h₃ := domain.length_le
    have h₄ := selected.length_le
    simp only [compatibleAcc, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def compatible (ones zeros domain selected : IndexedMask n) : Bool × ℕ :=
  let r := compatibleAcc ones zeros domain selected (List.finRange n)
  (r.1, r.2 + n + 1)

theorem compatible_value (ones zeros domain selected : IndexedMask n) :
    (compatible ones zeros domain selected).1 =
      (MaskRestriction.mk ones.semantic zeros.semantic).accept domain.semantic selected.semantic := by
  apply Bool.eq_iff_iff.mpr
  simp only [compatible, compatibleAcc_value, List.mem_finRange, forall_true_left,
    MaskRestriction.accept_eq_true, MaskRestriction.Compatible, Finset.subset_iff,
    Finset.mem_inter, Finset.disjoint_left, semantic, List.mem_toFinset]
  constructor
  · intro h
    exact ⟨fun i hi => (h i).1 hi, fun i hi hs => (h i).2 ⟨hi, hs⟩⟩
  · rintro ⟨h₁, h₂⟩ i
    exact ⟨fun h => h₁ h, fun h => h₂ h.1 h.2⟩

theorem compatible_work (ones zeros domain selected : IndexedMask n) :
    (compatible ones zeros domain selected).2 ≤ (4 * n + 12) * n + n + 2 := by
  have h := compatibleAcc_work ones zeros domain selected (List.finRange n)
  simp only [List.length_finRange] at h
  change (compatibleAcc ones zeros domain selected (List.finRange n)).2 + n + 1 ≤ _
  omega

theorem compatible_scale (I : Instance n) (ones zeros domain selected : IndexedMask n)
    (hn : 10000 ≤ n) : (compatible ones zeros domain selected).2 ≤ inputScale I ^ 3 := by
  have h := compatible_work ones zeros domain selected
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hs := Nat.pow_le_pow_left hnu 2
  have hm := Nat.mul_le_mul_right (inputScale I ^ 2)
    (show 20 ≤ inputScale I by omega)
  have hsmall : (4 * n + 12) * n + n + 2 ≤ 20 * (n + 1) ^ 2 := by nlinarith
  have hp : 20 * (n + 1) ^ 2 ≤ inputScale I ^ 3 := by nlinarith only [hs, hm]
  exact h.trans (hsmall.trans hp)

end IndexedMask

namespace MeasuredFilter

variable {α : Type*}

/-- The accumulator retains output order after one final reversal. -/
def runAcc (test : α → Bool × ℕ) : List α → List α → ℕ → List α × ℕ
  | [], acc, work => (acc.reverse, work + acc.length + 1)
  | x :: xs, acc, work =>
    let p := test x
    runAcc test xs (if p.1 then x :: acc else acc) (work + p.2 + 3)

theorem runAcc_value (test : α → Bool × ℕ) (xs acc : List α) (work : ℕ) :
    (runAcc test xs acc work).1 = acc.reverse ++ xs.filter (fun x => (test x).1) := by
  induction xs generalizing acc work with
  | nil => simp [runAcc]
  | cons x xs ih =>
    simp only [runAcc, ih, List.filter_cons]
    cases (test x).1 <;> simp [List.reverse_cons, List.append_assoc]

theorem runAcc_work (test : α → Bool × ℕ) (K : ℕ) (hk : ∀ x, (test x).2 ≤ K)
    (xs acc : List α) (work : ℕ) :
    (runAcc test xs acc work).2 ≤ work + (K + 4) * xs.length + acc.length + 1 := by
  induction xs generalizing acc work with
  | nil => simp [runAcc]
  | cons x xs ih =>
    have hx := hk x
    simp only [runAcc, List.length_cons, Nat.mul_add, Nat.mul_one]
    cases (test x).1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h := ih acc (work + (test x).2 + 3)
      omega
    · simp only [↓reduceIte]
      have h := ih (x :: acc) (work + (test x).2 + 3)
      simp only [List.length_cons] at h
      omega

def array (test : α → Bool × ℕ) (xs : List α) : Array α × ℕ :=
  let r := runAcc test xs [] 0
  (r.1.toArray, r.2 + r.1.length)

theorem array_value (test : α → Bool × ℕ) (xs : List α) :
    (array test xs).1 = (xs.filter (fun x => (test x).1)).toArray := by
  simp only [array, runAcc_value, List.reverse_nil, List.nil_append]

theorem array_work (test : α → Bool × ℕ) (K : ℕ) (hk : ∀ x, (test x).2 ≤ K)
    (xs : List α) : (array test xs).2 ≤ (K + 5) * xs.length + 1 := by
  have h := runAcc_work test K hk xs [] 0
  have hl := List.length_filter_le (fun x => (test x).1) xs
  simp only [array, runAcc_value, List.reverse_nil, List.nil_append]
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero] at h
  nlinarith only [h, hl]

end MeasuredFilter
end LowSpaceSubsetSum

end OAI
