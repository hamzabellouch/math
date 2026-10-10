import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorTraversalCost
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorStoredMasks
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorTerminal

namespace OAI

/-! # Composition of the separator's four interval traversals -/

namespace LowSpaceSubsetSum.SeparatorBlocks

open SeparatorTraversal SeparatorIncidenceTable

variable {α β : Type*}

structure Block (α β : Type*) where
  size : ℕ
  left : α → Array ℕ
  right : β → Array ℕ
  left_sorted : ∀ x, Monotone (fun i : Fin (left x).size => (left x)[i.val])
  right_sorted : ∀ y, Monotone (fun i : Fin (right y).size => (right y)[i.val])

def depth (b : Block α β) : ℕ := Nat.clog 2 b.size

theorem transport_sorted (a b : Array ℕ) (he : a = b)
    (hs : Monotone (fun i : Fin a.size => a[i.val])) :
    Monotone (fun i : Fin b.size => b[i.val]) := by
  subst b
  exact hs

/-- Family tables are computed once, then captured by the lookup functions.
The runtime interval loop only indexes these stored arrays. -/
def ofFamily {g : ℕ} (family : Array (Finset (Fin g)))
    (mask₁ : α → Finset (Fin g)) (mask₂ : β → Finset (Fin g)) : Block α β :=
  let leftStore := SeparatorStoredMasks.containsStore family
  let rightStore := SeparatorStoredMasks.avoidsStore family
  { size := family.size
    left := fun x => SeparatorStoredMasks.containsList leftStore
      (SeparatorStoredMasks.containsStore_size family) (mask₁ x)
    right := fun y => SeparatorStoredMasks.avoidsList rightStore
      (SeparatorStoredMasks.avoidsStore_size family) (mask₂ y)
    left_sorted := fun x => by
      exact transport_sorted _ _ (SeparatorStoredMasks.containsList_eq family (mask₁ x)).symm
        (table_monotone _ _ _)
    right_sorted := fun y => by
      exact transport_sorted _ _ (SeparatorStoredMasks.avoidsList_eq family (mask₂ y)).symm
        (table_monotone _ _ _) }

def PairGood (blocks : List (Block α β)) (x : α) (y : β) : Prop :=
  ∀ b ∈ blocks, ∃ j < b.size, j ∈ (b.left x).toList ∧ j ∈ (b.right y).toList

def check (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ) :
    List (Block α β) → List α → List β → Result
  | [], xs, ys => SeparatorTerminal.bounded n wx wy target xs ys
  | b :: rest, xs, ys =>
    if xs.length + ys.length ≤ 2 ^ n then
      SeparatorTraversal.run b.left b.right (fun _ => check n wx wy target rest)
        (depth b) 0 b.size xs ys
    else ⟨false, 0, 0⟩

theorem correct (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (blocks : List (Block α β)) (xs : List α) (ys : List β)
    (hsize : xs.length + ys.length ≤ 2 ^ n) :
    (check n wx wy target blocks xs ys).accepted = true ↔
      ∃ x ∈ xs, ∃ y ∈ ys, PairGood blocks x y ∧ wx x + wy y = target := by
  induction blocks generalizing xs ys with
  | nil =>
    simpa only [check, PairGood, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      true_and] using SeparatorTerminal.bounded_correct n wx wy target xs ys hsize
  | cons b rest ih =>
    simp only [check, hsize, ↓reduceIte]
    rw [SeparatorTraversal.correct b.left b.right (fun _ => check n wx wy target rest)
      (fun x y => PairGood rest x y ∧ wx x + wy y = target)
      b.left_sorted b.right_sorted (2 ^ n) (fun _ xs ys hs => ih xs ys hs)
      (depth b) 0 b.size xs ys
      (by simpa only [Nat.sub_zero, depth] using Nat.le_pow_clog (by decide : 1 < 2) b.size)
      hsize]
    constructor
    · rintro ⟨j, _, hj, x, hx, y, hy, hxl, hyl, hr, hw⟩
      refine ⟨x, hx, y, hy, ?_, hw⟩
      intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact ⟨j, hj, hxl, hyl⟩
      · exact hr b' hb'
    · rintro ⟨x, hx, y, hy, hp, hw⟩
      obtain ⟨j, hj, hxl, hyl⟩ := hp b (by simp)
      exact ⟨j, Nat.zero_le _, hj, x, hx, y, hy, hxl, hyl,
        (fun b' hb' => hp b' (by simp [hb'])), hw⟩

def chargeLeft (n : ℕ) : List (Block α β) → α → ℕ
  | [], _ => 6 * n + 7
  | b :: rest, x => 1 + (2 * depth b + chargeLeft n rest x) * count (b.left x) 0 b.size

def chargeRight (n : ℕ) : List (Block α β) → β → ℕ
  | [], _ => 6 * n + 7
  | b :: rest, y => 1 + (2 * depth b + chargeRight n rest y) * count (b.right y) 0 b.size

theorem sum_charge {γ : Type*} (inc : γ → Array ℕ) (charge : γ → ℕ) (zs : List γ)
    (d size : ℕ) :
    (zs.map (fun z => 1 + (2 * d + charge z) * count (inc z) 0 size)).sum =
      zs.length + 2 * d * mass inc 0 size zs (fun _ => 1) + mass inc 0 size zs charge := by
  induction zs with
  | nil => simp [mass]
  | cons z zs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, mass] at *
    nlinarith

theorem scans_le (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (blocks : List (Block α β)) (xs : List α) (ys : List β) :
    (check n wx wy target blocks xs ys).scans ≤
      (xs.map (chargeLeft n blocks)).sum + (ys.map (chargeRight n blocks)).sum := by
  induction blocks generalizing xs ys with
  | nil =>
    simpa [check, chargeLeft, chargeRight, List.map_const', List.sum_replicate, nsmul_eq_mul,
      Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      SeparatorTerminal.bounded_scans n wx wy target xs ys
  | cons b rest ih =>
    simp only [check]
    split_ifs
    · have h := SeparatorTraversal.scans_le b.left b.right
        (fun _ => check n wx wy target rest) b.left_sorted b.right_sorted
        (chargeLeft n rest) (chargeRight n rest) (fun _ => ih)
        (depth b) 0 b.size xs ys
      change _ ≤ (xs.map (fun x => 1 + (2 * depth b + chargeLeft n rest x) *
        count (b.left x) 0 b.size)).sum + (ys.map (fun y => 1 +
        (2 * depth b + chargeRight n rest y) * count (b.right y) 0 b.size)).sum
      rw [sum_charge b.left (chargeLeft n rest) xs (depth b) b.size,
        sum_charge b.right (chargeRight n rest) ys (depth b) b.size]
      nlinarith
    · dsimp
      omega

def peakBound (n : ℕ) (blocks : List (Block α β)) : ℕ :=
  2 * 2 ^ n * ((blocks.map (fun b => depth b + 1)).sum) + 8 * (n + 1) * (2 ^ n + 1)

theorem peak_le (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (blocks : List (Block α β)) (xs : List α) (ys : List β) :
    (check n wx wy target blocks xs ys).peak ≤ peakBound n blocks := by
  induction blocks generalizing xs ys with
  | nil => simpa [check, peakBound] using SeparatorTerminal.bounded_peak n wx wy target xs ys
  | cons b rest ih =>
    simp only [check]
    split_ifs with hsize
    · have h := SeparatorTraversal.peak_le b.left b.right (fun _ => check n wx wy target rest)
        (peakBound n rest) (fun _ => ih) (depth b) 0 b.size xs ys
      simp only [peakBound, List.map_cons, List.sum_cons] at h ⊢
      nlinarith
    · dsimp
      exact Nat.zero_le _

def capacityPeak (n C : ℕ) (blocks : List (Block α β)) : ℕ :=
  2 * C * ((blocks.map (fun b => depth b + 1)).sum) + 8 * (n + 1) * (C + 1)

theorem peak_capacity (n C : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (blocks : List (Block α β)) (xs : List α) (ys : List β)
    (hsize : xs.length + ys.length ≤ C) (hC : C ≤ 2 ^ n) :
    (check n wx wy target blocks xs ys).peak ≤ capacityPeak n C blocks := by
  induction blocks generalizing xs ys with
  | nil => simpa [check, capacityPeak] using
      SeparatorTerminal.bounded_peak_capacity n C wx wy target xs ys hsize hC
  | cons b rest ih =>
    simp only [check, hsize.trans hC, ↓reduceIte]
    have h := SeparatorTraversal.peak_le_capacity b.left b.right
      (fun _ => check n wx wy target rest) C (capacityPeak n C rest)
      (fun _ xs ys hs => ih xs ys hs) (depth b) 0 b.size xs ys hsize
    simp only [capacityPeak, List.map_cons, List.sum_cons] at h ⊢
    nlinarith

end LowSpaceSubsetSum.SeparatorBlocks

end OAI
