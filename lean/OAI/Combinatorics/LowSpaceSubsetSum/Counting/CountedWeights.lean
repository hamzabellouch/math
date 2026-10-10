import OAI.Combinatorics.LowSpaceSubsetSum.Streams.WeightEncoding

namespace OAI

/-! # Indexed membership, signed sums and fixed-width key generation

The runtime mask is an indexed list; its finite set is only a proof view.
The operation tally counts index comparisons, addition, testBit and list
construction. Numerical values occupy the word widths proved separately.
Every finite indexed mask is permitted, including repeated input values.
-/

namespace LowSpaceSubsetSum.CountedWeights

variable {n : ℕ}

def member (i : Fin n) : List (Fin n) → Bool × ℕ
  | [] => (false, 1)
  | j :: xs =>
    if i = j then (true, 1) else
      let rest := member i xs
      (rest.1, rest.2 + 1)

theorem member_value (i : Fin n) (xs : List (Fin n)) :
    (member i xs).1 = decide (i ∈ xs) := by
  induction xs with
  | nil => simp [member]
  | cons j xs ih => by_cases h : i = j <;> simp [member, h, ih]

theorem member_work (i : Fin n) (xs : List (Fin n)) :
    (member i xs).2 ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [member]
  | cons j xs ih => simp only [member, List.length_cons]; split <;> dsimp only <;> omega

def sumIndices (a : Fin n → ℤ) (mask : List (Fin n)) : List (Fin n) → ℤ × ℕ
  | [] => (0, 1)
  | i :: xs =>
    let hit := member i mask
    let rest := sumIndices a mask xs
    ((if hit.1 then a i else 0) + rest.1, hit.2 + rest.2 + 3)

theorem sumIndices_value (a : Fin n → ℤ) (mask : List (Fin n)) (xs : List (Fin n)) :
    (sumIndices a mask xs).1 = (xs.map (fun i => if i ∈ mask then a i else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [sumIndices, member_value, decide_eq_true_eq,
      List.map_cons, List.sum_cons, ih]

theorem sumIndices_work (a : Fin n → ℤ) (mask : List (Fin n)) (xs : List (Fin n)) :
    (sumIndices a mask xs).2 ≤ (mask.length + 4) * xs.length + 1 := by
  induction xs with
  | nil => simp [sumIndices]
  | cons i xs ih =>
    have hm := member_work i mask
    simp only [sumIndices, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def weight (a : Fin n → ℤ) (mask : List (Fin n)) : ℤ × ℕ :=
  sumIndices a mask (List.ofFn id)

theorem weight_value (a : Fin n → ℤ) (mask : List (Fin n)) :
    (weight a mask).1 = LowSpaceSubsetSum.weight a mask.toFinset := by
  rw [weight, sumIndices_value]
  simp only [List.map_ofFn, Function.comp_id, List.sum_ofFn, LowSpaceSubsetSum.weight, List.mem_toFinset]

theorem weight_work (a : Fin n → ℤ) (mask : List (Fin n)) :
    (weight a mask).2 ≤ (mask.length + 4) * n + 1 := by
  have h := sumIndices_work a mask (List.ofFn id)
  simp only [List.length_ofFn] at h
  exact h

def maskIndices (mask : List (Fin n)) : List (Fin n) → List Bool × ℕ
  | [] => ([], 1)
  | i :: xs =>
    let hit := member i mask
    let rest := maskIndices mask xs
    (hit.1 :: rest.1, hit.2 + rest.2 + 2)

theorem maskIndices_value (mask : List (Fin n)) (xs : List (Fin n)) :
    (maskIndices mask xs).1 = xs.map (fun i => decide (i ∈ mask)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [maskIndices, member_value, ih, List.map_cons]

theorem maskIndices_work (mask : List (Fin n)) (xs : List (Fin n)) :
    (maskIndices mask xs).2 ≤ (mask.length + 3) * xs.length + 1 := by
  induction xs with
  | nil => simp [maskIndices]
  | cons i xs ih =>
    have hm := member_work i mask
    simp only [maskIndices, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def maskBits (mask : List (Fin n)) : List Bool × ℕ := maskIndices mask (List.ofFn id)

theorem maskBits_value (mask : List (Fin n)) :
    (maskBits mask).1 = WeightEncoding.maskBits mask.toFinset := by
  rw [maskBits, maskIndices_value]
  simp only [List.map_ofFn, Function.comp_id, WeightEncoding.maskBits, List.mem_toFinset]

theorem maskBits_work (mask : List (Fin n)) :
    (maskBits mask).2 ≤ (mask.length + 3) * n + 1 := by
  have h := maskIndices_work mask (List.ofFn id)
  simp only [List.length_ofFn] at h
  exact h

/-- Each output bit uses one testBit operation and one list record. -/
def bits (value : ℕ) : ℕ → ℕ → List Bool × ℕ
  | 0, _ => ([], 1)
  | k + 1, start =>
    let rest := bits value k (start + 1)
    (value.testBit start :: rest.1, rest.2 + 3)

theorem bits_value (value k start : ℕ) :
    (bits value k start).1 = List.ofFn (fun i : Fin k => value.testBit (start + i.val)) := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    simp only [bits, ih, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    congr 1
    funext i
    congr 1
    omega

theorem bits_work (value k start : ℕ) : (bits value k start).2 = 3 * k + 1 := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp only [bits, ih]; omega

def natBits (width value : ℕ) : List Bool × ℕ := bits value width 0

theorem natBits_value (width value : ℕ) :
    (natBits width value).1 = WeightEncoding.natBits width value := by
  simp only [natBits, bits_value, Nat.zero_add, WeightEncoding.natBits]

def entryKey (I : Instance n) (value : ℤ) (mask : List (Fin n)) : List Bool × ℕ :=
  let mag := natBits (2 * inputScale I) value.natAbs
  let bits := maskBits mask
  (decide (value < 0) :: (mag.1 ++ bits.1), mag.2 + bits.2 + 2 * inputScale I + 3)

theorem entryKey_value (I : Instance n) (value : ℤ) (mask : List (Fin n)) :
    (entryKey I value mask).1 = WeightEncoding.entryKey I ⟨value, mask.toFinset⟩ := by
  simp only [entryKey, natBits_value, maskBits_value,
    WeightEncoding.entryKey, WeightEncoding.weightKey, WeightEncoding.signedBits, List.cons_append]

theorem entryKey_work (I : Instance n) (value : ℤ) (mask : List (Fin n)) (hmask : mask.length ≤ n) :
    (entryKey I value mask).2 ≤ 12 * inputScale I ^ 2 := by
  have hm := maskBits_work mask
  have hn : n ≤ inputScale I := by unfold inputScale; omega
  have hu : 2 ≤ inputScale I := by unfold inputScale; omega
  have hs : n ^ 2 ≤ inputScale I ^ 2 := Nat.pow_le_pow_left hn 2
  have hp := Nat.mul_le_mul_right n (Nat.add_le_add_right hmask 3)
  simp only [entryKey, natBits, bits_work]
  nlinarith only [hm, hn, hu, hs, hp]

end LowSpaceSubsetSum.CountedWeights

end OAI
