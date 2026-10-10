import OAI.Combinatorics.EditApproximation.Numerics.ScalarControlSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryLoopSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Allocation and invocation traces for the actual Boolean logarithm,
dot-product, and gradient loops. Constant literal words are shared. -/

namespace EditApproximation.BinaryFraction



def subInvocations (a b : BinaryFraction) : ℕ := canonicalAddInvocations a b.neg + 1

theorem subAllocation_le_work (a b : BinaryFraction) :
    subAllocation a b ≤ (subWithWork a b).2 := by
  have h := canonicalAddAllocation_le_work a b.neg
  unfold subAllocation subWithWork
  dsimp only
  omega

theorem subInvocations_le_work (a b : BinaryFraction) :
    subInvocations a b ≤ (subWithWork a b).2 := by
  exact Nat.add_le_add_right (canonicalAddInvocations_le_work a b.neg) 1



def powInvocations (a : BinaryFraction) : ℕ → ℕ
  | 0 => 1
  | n + 1 => powInvocations a n + canonicalMulInvocations (powWithWork a n).1 a + 1

theorem powAllocation_le_work (a : BinaryFraction) (n : ℕ) :
    powAllocation a n ≤ (powWithWork a n).2 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := canonicalMulAllocation_le_work (powWithWork a n).1 a
    simp only [powAllocation, powWithWork]
    exact (Nat.add_le_add ih h).trans (Nat.le_succ _)

theorem powInvocations_le_work (a : BinaryFraction) (n : ℕ) :
    powInvocations a n ≤ (powWithWork a n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := canonicalMulInvocations_le_work (powWithWork a n).1 a
    simp only [powInvocations, powWithWork]
    omega



def logarithmPartialInvocations (b : BinaryFraction) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let previous := (logarithmPartialWithWork b n).1
    let power := (powWithWork b (2 * n + 1)).1
    let term := (divWithWork power (nat (2 * n + 1))).1
    logarithmPartialInvocations b n + powInvocations b (2 * n + 1) +
      divInvocations power (nat (2 * n + 1)) + canonicalAddInvocations previous term + 1

theorem logarithmPartialAllocation_le_work (b : BinaryFraction) (n : ℕ) :
    logarithmPartialAllocation b n ≤ (logarithmPartialWithWork b n).2 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hp := powAllocation_le_work b (2 * n + 1)
    have hd := divAllocation_le_work (powWithWork b (2 * n + 1)).1 (nat (2 * n + 1))
    have ha := canonicalAddAllocation_le_work (logarithmPartialWithWork b n).1
      (divWithWork (powWithWork b (2 * n + 1)).1 (nat (2 * n + 1))).1
    simp only [logarithmPartialAllocation, logarithmPartialWithWork]
    exact Nat.add_le_add
      (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ih hp) hd) ha) _)
      (by decide : 1 ≤ 5)

theorem logarithmPartialInvocations_le_work (b : BinaryFraction) (n : ℕ) :
    logarithmPartialInvocations b n ≤ (logarithmPartialWithWork b n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := powInvocations_le_work b (2 * n + 1)
    have hd := divInvocations_le_work (powWithWork b (2 * n + 1)).1 (nat (2 * n + 1))
    have ha := canonicalAddInvocations_le_work (logarithmPartialWithWork b n).1
      (divWithWork (powWithWork b (2 * n + 1)).1 (nat (2 * n + 1))).1
    simp only [logarithmPartialInvocations, logarithmPartialWithWork]
    omega



def logarithmInvocations (r : BinaryFraction) (n : ℕ) : ℕ :=
  let numerator := (subWithWork r one).1
  let denominator := (canonicalAddWithWork r one).1
  let ratio := (divWithWork numerator denominator).1
  subInvocations r one + canonicalAddInvocations r one + divInvocations numerator denominator +
    logarithmPartialInvocations ratio n + canonicalMulInvocations (nat 2) (logarithmPartialWithWork ratio n).1 + 1

theorem logarithmAllocation_le_work (r : BinaryFraction) (n : ℕ) :
    logarithmAllocation r n ≤ (logarithmWithWork r n).2 := by
  have h1 := subAllocation_le_work r one
  have h2 := canonicalAddAllocation_le_work r one
  have h3 := divAllocation_le_work (subWithWork r one).1 (canonicalAddWithWork r one).1
  have h4 := logarithmPartialAllocation_le_work (divWithWork (subWithWork r one).1 (canonicalAddWithWork r one).1).1 n
  have h5 := canonicalMulAllocation_le_work (nat 2)
    (logarithmPartialWithWork (divWithWork (subWithWork r one).1 (canonicalAddWithWork r one).1).1 n).1
  unfold logarithmAllocation logarithmWithWork
  dsimp only
  omega

theorem logarithmInvocations_le_work (r : BinaryFraction) (n : ℕ) :
    logarithmInvocations r n ≤ (logarithmWithWork r n).2 := by
  have h1 := subInvocations_le_work r one
  have h2 := canonicalAddInvocations_le_work r one
  have h3 := divInvocations_le_work (subWithWork r one).1 (canonicalAddWithWork r one).1
  have h4 := logarithmPartialInvocations_le_work (divWithWork (subWithWork r one).1 (canonicalAddWithWork r one).1).1 n
  have h5 := canonicalMulInvocations_le_work (nat 2)
    (logarithmPartialWithWork (divWithWork (subWithWork r one).1 (canonicalAddWithWork r one).1).1 n).1
  unfold logarithmInvocations logarithmWithWork
  dsimp only
  omega



def dotListInvocations {d : ℕ} (left right : Vector BinaryFraction d) : List (Fin d) → ℕ
  | [] => 1
  | i :: rest => dotListInvocations left right rest +
      canonicalMulInvocations (left.get i) (right.get i) +
      canonicalAddInvocations (canonicalMulWithWork (left.get i) (right.get i)).1 (dotListWithWork left right rest).1 + 1

theorem dotListAllocation_le_work {d : ℕ} (left right : Vector BinaryFraction d) (indices : List (Fin d)) :
    dotListAllocation left right indices ≤ (dotListWithWork left right indices).2 := by
  induction indices with
  | nil => simp only [dotListAllocation, dotListWithWork, Nat.zero_le]
  | cons i rest ih =>
    have hm := canonicalMulAllocation_le_work (left.get i) (right.get i)
    have ha := canonicalAddAllocation_le_work
      (canonicalMulWithWork (left.get i) (right.get i)).1 (dotListWithWork left right rest).1
    simp only [dotListAllocation, dotListWithWork]
    omega

theorem dotListInvocations_le_work {d : ℕ} (left right : Vector BinaryFraction d) (indices : List (Fin d)) :
    dotListInvocations left right indices ≤ (dotListWithWork left right indices).2 := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have hm := canonicalMulInvocations_le_work (left.get i) (right.get i)
    have ha := canonicalAddInvocations_le_work
      (canonicalMulWithWork (left.get i) (right.get i)).1 (dotListWithWork left right rest).1
    simp only [dotListInvocations, dotListWithWork]
    omega



def gradientCellInvocations {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (i : Fin d) : ℕ :=
  let smoothing := (powWithWork (nat G) 50).1
  let inverse := smoothing.invWithWork.1
  let shifted := (canonicalAddWithWork (point.get i) inverse).1
  let logarithm := (logarithmWithWork shifted (G ^ 60)).1
  let deficit := (subWithWork logarithm.neg one).1
  powInvocations (nat G) 50 + invInvocations smoothing +
    canonicalAddInvocations (point.get i) inverse + logarithmInvocations shifted (G ^ 60) +
    subInvocations logarithm.neg one + canonicalAddInvocations deficit (linear.get i) + 1

theorem gradientCellAllocation_le_work {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    gradientCellAllocation G linear point i ≤ (gradientCellWithWork G linear point i).2 := by
  have h1 := powAllocation_le_work (nat G) 50
  have h2 := invAllocation_le_work (powWithWork (nat G) 50).1
  have h3 := canonicalAddAllocation_le_work (point.get i) (powWithWork (nat G) 50).1.invWithWork.1
  have h4 := logarithmAllocation_le_work
    (canonicalAddWithWork (point.get i) (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)
  have h5 := subAllocation_le_work
    (logarithmWithWork (canonicalAddWithWork (point.get i)
      (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)).1.neg one
  have h6 := canonicalAddAllocation_le_work
    (subWithWork (logarithmWithWork (canonicalAddWithWork (point.get i)
      (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)).1.neg one).1 (linear.get i)
  unfold gradientCellAllocation gradientCellWithWork
  dsimp only
  omega

theorem gradientCellInvocations_le_work {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    gradientCellInvocations G linear point i ≤ (gradientCellWithWork G linear point i).2 := by
  have h1 := powInvocations_le_work (nat G) 50
  have h2 := invInvocations_le_work (powWithWork (nat G) 50).1
  have h3 := canonicalAddInvocations_le_work (point.get i) (powWithWork (nat G) 50).1.invWithWork.1
  have h4 := logarithmInvocations_le_work
    (canonicalAddWithWork (point.get i) (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)
  have h5 := subInvocations_le_work
    (logarithmWithWork (canonicalAddWithWork (point.get i)
      (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)).1.neg one
  have h6 := canonicalAddInvocations_le_work
    (subWithWork (logarithmWithWork (canonicalAddWithWork (point.get i)
      (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)).1.neg one).1 (linear.get i)
  unfold gradientCellInvocations gradientCellWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
