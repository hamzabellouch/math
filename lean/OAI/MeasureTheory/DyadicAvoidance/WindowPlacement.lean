import Mathlib

namespace OAI

universe u_α

open scoped BigOperators

namespace Problem310.WindowPlacement

/-- Place windows in preorder, reserving `g` unused indices after each window. -/
def start (len : ℕ → ℕ) (g : ℕ) : ℕ → ℕ
  | 0 => 3
  | i + 1 => start len g i + len i + g

def finish (len : ℕ → ℕ) (g i : ℕ) : ℕ := start len g i + len i - 1

def window (len : ℕ → ℕ) (g i : ℕ) : Finset ℕ :=
  Finset.Icc (start len g i) (finish len g i)

/-- Extract a window length from a finite preorder list, using zero outside the list. -/
def lengthAt (L : List ℕ) (i : ℕ) : ℕ := L[i]?.getD 0

theorem lengthAt_map_of_getElem? {α : Type u_α} (f : α → ℕ)
    {L : List α} {i : ℕ} {x : α} (h : L[i]? = some x) :
    lengthAt (L.map f) i = f x := by
  simp only [lengthAt, List.getElem?_map, h, Option.map_some, Option.getD_some]

theorem lengthAt_map_idxOf {α : Type u_α} [BEq α] [LawfulBEq α]
    (f : α → ℕ) {L : List α} {x : α} (hx : x ∈ L) :
    lengthAt (L.map f) (L.idxOf x) = f x :=
  lengthAt_map_of_getElem? f (List.getElem?_idxOf hx)

theorem lengthAt_pos {L : List ℕ} {i : ℕ} (hi : i < L.length)
    (hL : ∀ r ∈ L, 0 < r) : 0 < lengthAt L i := by
  simp only [lengthAt, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hL _ (List.getElem_mem hi)

theorem sum_lengthAt (L : List ℕ) :
    (∑ i ∈ Finset.range L.length, lengthAt L i) = L.sum := by
  induction L with
  | nil => simp [lengthAt]
  | cons a L ih =>
      simp only [List.length_cons, Finset.sum_range_succ', lengthAt,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        List.sum_cons]
      change (∑ i ∈ Finset.range L.length, lengthAt L i) + a = a + L.sum
      rw [ih, Nat.add_comm]

theorem lengthAt_segment (pre block post : List ℕ) {k : ℕ} (hk : k < block.length) :
    lengthAt (pre ++ block ++ post) (pre.length + k) = lengthAt block k := by
  simp only [lengthAt, List.append_assoc, List.getElem?_append]
  rw [ite_eq_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [ite_eq_left hk]

/-- Translate a consecutive preorder block's list sum into the prefix-sum
interface used by the endpoint and resolution lemmas. -/
theorem sum_lengthAt_segment (pre block post : List ℕ) (g : ℕ) :
    (∑ k ∈ Finset.range block.length,
      (lengthAt (pre ++ block ++ post) (pre.length + k) + g)) =
      (block.map (fun r => r + g)).sum := by
  calc
    _ = ∑ k ∈ Finset.range block.length, (lengthAt block k + g) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [lengthAt_segment pre block post (Finset.mem_range.mp hk)]
    _ = block.sum + block.length * g := by
      rw [Finset.sum_add_distrib, sum_lengthAt]
      simp
    _ = _ := by
      induction block with
      | nil => simp
      | cons a block ih =>
          simp only [List.sum_cons, List.length_cons, List.map_cons]
          rw [← ih]
          simp only [Nat.add_mul, Nat.one_mul]
          omega

@[simp] theorem start_zero (len : ℕ → ℕ) (g : ℕ) : start len g 0 = 3 := rfl

@[simp] theorem start_succ (len : ℕ → ℕ) (g i : ℕ) :
    start len g (i + 1) = start len g i + len i + g := rfl

theorem start_mono (len : ℕ → ℕ) (g : ℕ) : Monotone (start len g) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [start_succ]
  omega

theorem three_le_start (len : ℕ → ℕ) (g i : ℕ) : 3 ≤ start len g i := by
  simpa using start_mono len g (Nat.zero_le i)

theorem finish_add_one (len : ℕ → ℕ) (g i : ℕ) :
    finish len g i + 1 = start len g i + len i := by
  have := three_le_start len g i
  unfold finish
  omega

/-- Endpoints are nondecreasing even if some windows have length zero. -/
theorem finish_mono (len : ℕ → ℕ) (g : ℕ) : Monotone (finish len g) := by
  apply monotone_nat_of_le_succ
  intro i
  have hi := finish_add_one len g i
  have hj := finish_add_one len g (i + 1)
  rw [start_succ] at hj
  omega

theorem consecutive_gap (len : ℕ → ℕ) (g i : ℕ) :
    start len g (i + 1) = finish len g i + g + 1 := by
  rw [start_succ]
  have := finish_add_one len g i
  omega

/-- Every later window starts strictly beyond the earlier endpoint and its gap. -/
theorem gap_of_lt (len : ℕ → ℕ) (g : ℕ) {i j : ℕ} (hij : i < j) :
    finish len g i + g < start len g j := by
  have hm := start_mono len g (Nat.succ_le_of_lt hij)
  rw [consecutive_gap] at hm
  omega

theorem finish_lt_start (len : ℕ → ℕ) (g : ℕ) {i j : ℕ} (hij : i < j) :
    finish len g i < start len g j := by
  have := gap_of_lt len g hij
  omega

theorem start_le_finish {len : ℕ → ℕ} {g i : ℕ} (hi : 0 < len i) :
    start len g i ≤ finish len g i := by
  have := finish_add_one len g i
  omega

theorem finish_lt_of_lt {len : ℕ → ℕ} {g i j : ℕ}
    (hij : i < j) (hj : 0 < len j) : finish len g i < finish len g j :=
  (finish_lt_start len g hij).trans_le (start_le_finish hj)

theorem finish_le_of_le {len : ℕ → ℕ} {g i j : ℕ}
    (hij : i ≤ j) (hj : 0 < len j) : finish len g i ≤ finish len g j := by
  rcases hij.eq_or_lt with rfl | hij
  · rfl
  · exact (finish_lt_of_lt hij hj).le

theorem finish_strictMono {len : ℕ → ℕ} (g : ℕ) (hlen : ∀ i, 0 < len i) :
    StrictMono (finish len g) := fun _ j hij => finish_lt_of_lt hij (hlen j)

@[simp] theorem mem_window {len : ℕ → ℕ} {g i n : ℕ} :
    n ∈ window len g i ↔ start len g i ≤ n ∧ n ≤ finish len g i :=
  Finset.mem_Icc

theorem three_le_of_mem {len : ℕ → ℕ} {g i n : ℕ}
    (hn : n ∈ window len g i) : 3 ≤ n :=
  (three_le_start len g i).trans (mem_window.mp hn).1

theorem indices_separated {len : ℕ → ℕ} {g i j n m : ℕ}
    (hij : i < j) (hn : n ∈ window len g i) (hm : m ∈ window len g j) : n + g < m := by
  have hb := gap_of_lt len g hij
  have hni := (mem_window.mp hn).2
  have hmj := (mem_window.mp hm).1
  omega

theorem disjoint_windows (len : ℕ → ℕ) (g : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (window len g i) (window len g j) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  rcases lt_or_gt_of_ne hij with h | h
  · have := indices_separated h hn hm
    omega
  · have := indices_separated h hm hn
    omega

@[simp] theorem card_window (len : ℕ → ℕ) (g i : ℕ) :
    (window len g i).card = len i := by
  rw [window, Nat.card_Icc]
  have := finish_add_one len g i
  omega

/-- Disjoint windows contribute exactly the sum of their lengths. -/
theorem card_windows (len : ℕ → ℕ) (g : ℕ) (S : Finset ℕ) :
    (S.biUnion (window len g)).card = ∑ i ∈ S, len i := by
  rw [Finset.card_biUnion]
  · simp only [card_window]
  · intro i _ j _ hij
    exact disjoint_windows len g hij

theorem card_equal_windows {len : ℕ → ℕ} (g : ℕ) (S : Finset ℕ) (r : ℕ)
    (hlen : ∀ i ∈ S, len i = r) :
    (S.biUnion (window len g)).card = S.card * r := by
  rw [card_windows]
  calc
    (∑ i ∈ S, len i) = ∑ _i ∈ S, r := Finset.sum_congr rfl hlen
    _ = S.card * r := by simp

/-- Prefix-sum formula relative to any incoming edge. -/
theorem start_add (len : ℕ → ℕ) (g i m : ℕ) :
    start len g (i + m) = start len g i +
      ∑ k ∈ Finset.range m, (len (i + k) + g) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, start_succ, ih, Finset.sum_range_succ]
      omega

/-- A consecutive child block's endpoint is exactly its total window and gap budget. -/
theorem block_endpoint (len : ℕ → ℕ) (g i m : ℕ) :
    finish len g (i + m) + g + 1 = start len g i +
      ∑ k ∈ Finset.range (m + 1), (len (i + k) + g) := by
  rw [← consecutive_gap]
  simpa only [Nat.add_assoc] using start_add len g i (m + 1)

theorem block_endpoint_le {len : ℕ → ℕ} {g i m r : ℕ}
    (hbudget : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) ≤ 2 * r + g) :
    finish len g (i + m) + 1 ≤ start len g i + 2 * r := by
  have := block_endpoint len g i m
  omega

/-- An endpoint anywhere in a child block satisfies the same padding bound;
no positivity assumptions on individual list entries are necessary. -/
theorem local_endpoint_bound {len : ℕ → ℕ} {g i m r j : ℕ}
    (hbudget : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) ≤ 2 * r + g)
    (hj : j ≤ i + m) :
    finish len g j + 1 ≤ start len g i + 2 * r := by
  have he := block_endpoint_le hbudget
  have hj' := finish_mono len g hj
  omega

/-- Convert a bound on the sum of a child block's padded lengths into the
subtree-resolution bound used by the scale discretization. -/
theorem block_padding {len : ℕ → ℕ} {g i m r : ℕ}
    (hlen : 0 < len (i + m))
    (hbudget : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) ≤ 2 * r + g) :
    finish len g (i + m) - start len g i + 1 ≤ 2 * r := by
  have heq := block_endpoint len g i m
  have hlow := start_mono len g (Nat.le_add_right i m)
  have hend := finish_add_one len g (i + m)
  omega

/-- Every grid in a child block has resolution controlled by the incoming window.
This is in the additive form required by the common-representative bound. -/
theorem local_resolution_bound {len : ℕ → ℕ} {g i m r j n : ℕ}
    (hlen : 0 < len (i + m))
    (hbudget : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) ≤ 2 * r + g)
    (hj : j ≤ i + m) (hn : start len g i ≤ n) :
    finish len g j + 2 ≤ n + (2 * r + 2) := by
  have he := block_endpoint_le hbudget
  have hj' := finish_le_of_le (g := g) hj hlen
  omega

end Problem310.WindowPlacement

end OAI
