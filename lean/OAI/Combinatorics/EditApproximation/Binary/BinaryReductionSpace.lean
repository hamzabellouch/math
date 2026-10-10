import OAI.Combinatorics.EditApproximation.Binary.BinaryNumericSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryWarmupAverage
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Actual reduction scratch: comparisons retain their cross-products;
sums retain all dot-product intermediates and the materialized vectors. -/

namespace EditApproximation.BinaryFraction

/-- Two materialized index/value list spines fit the dot loop's per-cell charge. -/
theorem dotListAllocation_with_spines_le_work {d : ℕ}
    (left right : Vector BinaryFraction d) (indices : List (Fin d)) :
    dotListAllocation left right indices + 2 * indices.length ≤ (dotListWithWork left right indices).2 := by
  induction indices with
  | nil => simp only [dotListAllocation, dotListWithWork, List.length_nil]; omega
  | cons i rest ih =>
    have hm := canonicalMulAllocation_le_work (left.get i) (right.get i)
    have ha := canonicalAddAllocation_le_work
      (canonicalMulWithWork (left.get i) (right.get i)).1 (dotListWithWork left right rest).1
    simp only [dotListAllocation, dotListWithWork, List.length_cons]
    omega

theorem dotListInvocations_with_spines_le_work {d : ℕ}
    (left right : Vector BinaryFraction d) (indices : List (Fin d)) :
    dotListInvocations left right indices + 2 * indices.length ≤ (dotListWithWork left right indices).2 := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have hm := canonicalMulInvocations_le_work (left.get i) (right.get i)
    have ha := canonicalAddInvocations_le_work
      (canonicalMulWithWork (left.get i) (right.get i)).1 (dotListWithWork left right rest).1
    simp only [dotListInvocations, dotListWithWork, List.length_cons]
    omega



def bandMassInvocations {M : ℕ} (mass : Vector BinaryFraction M) : ℕ :=
  dotListInvocations mass (Vector.replicate M one) (List.finRange M) + 2 * M

theorem bandMassAllocation_le_work {M : ℕ} (mass : Vector BinaryFraction M) :
    bandMassAllocation mass ≤ (bandMassTotalWithWork mass).2 := by
  simpa only [bandMassAllocation, bandMassTotalWithWork, dotWithWork, List.length_finRange] using
    dotListAllocation_with_spines_le_work mass (Vector.replicate M one) (List.finRange M)

theorem bandMassInvocations_le_work {M : ℕ} (mass : Vector BinaryFraction M) :
    bandMassInvocations mass ≤ (bandMassTotalWithWork mass).2 := by
  simpa only [bandMassInvocations, bandMassTotalWithWork, dotWithWork, List.length_finRange] using
    dotListInvocations_with_spines_le_work mass (Vector.replicate M one) (List.finRange M)



def minInvocations (a b : BinaryFraction) : ℕ := compareInvocations a b + 1

theorem minAllocation_le_work (a b : BinaryFraction) :
    minAllocation a b ≤ (minWithWork a b).2 := by
  exact (ltAllocation_le_work a b).trans (Nat.le_add_right _ _)

theorem minInvocations_le_work (a b : BinaryFraction) :
    minInvocations a b ≤ (minWithWork a b).2 :=
  Nat.add_le_add_right (compareInvocations_le_work a b) 1



def minimumInvocations (fallback : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 1
  | head :: rest => minimumInvocations fallback rest +
      minInvocations head (minimumWithWork fallback rest).1 + 1

theorem minimumAllocation_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    minimumAllocation fallback values ≤ (minimumWithWork fallback values).2 := by
  induction values with
  | nil => simp only [minimumAllocation, minimumWithWork, Nat.zero_le]
  | cons head rest ih =>
    have h := minAllocation_le_work head (minimumWithWork fallback rest).1
    simp only [minimumAllocation, minimumWithWork]
    omega

theorem minimumInvocations_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    minimumInvocations fallback values ≤ (minimumWithWork fallback values).2 := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    have h := minInvocations_le_work head (minimumWithWork fallback rest).1
    simp only [minimumInvocations, minimumWithWork]
    omega



def maxInvocations (a b : BinaryFraction) : ℕ := compareInvocations a b + 1

theorem maxAllocation_le_work (a b : BinaryFraction) :
    maxAllocation a b ≤ (maxWithWork a b).2 := by
  exact (ltAllocation_le_work a b).trans (Nat.le_add_right _ _)

theorem maxInvocations_le_work (a b : BinaryFraction) :
    maxInvocations a b ≤ (maxWithWork a b).2 :=
  Nat.add_le_add_right (compareInvocations_le_work a b) 1



def maximumInvocations (fallback : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 1
  | head :: rest => maximumInvocations fallback rest +
      maxInvocations head (maximumWithWork fallback rest).1 + 1

theorem maximumAllocation_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    maximumAllocation fallback values ≤ (maximumWithWork fallback values).2 := by
  induction values with
  | nil => simp only [maximumAllocation, maximumWithWork, Nat.zero_le]
  | cons head rest ih =>
    have h := maxAllocation_le_work head (maximumWithWork fallback rest).1
    simp only [maximumAllocation, maximumWithWork]
    omega

theorem maximumInvocations_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    maximumInvocations fallback values ≤ (maximumWithWork fallback values).2 := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    have h := maxInvocations_le_work head (maximumWithWork fallback rest).1
    simp only [maximumInvocations, maximumWithWork]
    omega



def sumListInvocations (values : List BinaryFraction) : ℕ :=
  dotListInvocations (Vector.ofFn values.get) (Vector.replicate values.length one)
    (List.finRange values.length) + 3 * values.length

theorem sumListAllocation_le_work (values : List BinaryFraction) :
    sumListAllocation values ≤ (sumListWithWork values).2 := by
  have h := dotListAllocation_le_work (Vector.ofFn values.get) (Vector.replicate values.length one)
    (List.finRange values.length)
  unfold sumListAllocation sumListWithWork bandMassTotalWithWork dotWithWork
  dsimp only
  omega

theorem sumListInvocations_le_work (values : List BinaryFraction) :
    sumListInvocations values ≤ (sumListWithWork values).2 := by
  have h := dotListInvocations_le_work (Vector.ofFn values.get) (Vector.replicate values.length one)
    (List.finRange values.length)
  unfold sumListInvocations sumListWithWork bandMassTotalWithWork dotWithWork
  dsimp only
  omega

def warmupAverageAllocation (values : List BinaryFraction) : ℕ :=
  sumListAllocation values + divAllocation (sumListWithWork values).1 (nat values.length) +
    Nat.size values.length + 1

def warmupAverageInvocations (values : List BinaryFraction) : ℕ :=
  sumListInvocations values + divInvocations (sumListWithWork values).1 (nat values.length) + 1

theorem warmupAverageAllocation_le_work (values : List BinaryFraction) :
    warmupAverageAllocation values ≤ (warmupAverageWithWork values).2 := by
  have hs := sumListAllocation_le_work values
  have hd := divAllocation_le_work (sumListWithWork values).1 (nat values.length)
  unfold warmupAverageAllocation warmupAverageWithWork
  dsimp only
  omega

theorem warmupAverageInvocations_le_work (values : List BinaryFraction) :
    warmupAverageInvocations values ≤ (warmupAverageWithWork values).2 := by
  have hs := sumListInvocations_le_work values
  have hd := divInvocations_le_work (sumListWithWork values).1 (nat values.length)
  unfold warmupAverageInvocations warmupAverageWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
