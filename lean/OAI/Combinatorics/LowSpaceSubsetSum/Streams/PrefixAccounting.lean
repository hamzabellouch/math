import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic

namespace OAI

/-!
# Deterministic accounting for right-prefix refinement

The tree depends on distinct entries for overflow, while raw tuple occurrences
are charged separately. The finite sets in this mathematical accounting are
ambient analysis sets, not arrays that the implementation is allowed to store.
The resulting combinatorial bounds give the accounting in `lem:prefix`.
-/

namespace LowSpaceSubsetSum

variable {α : Type*}

/-- Labels of the successive mask bits, in the fixed processing order. -/
abbrev MaskBits (α : Type*) := ℕ → α → Bool

def bitPart (bits : MaskBits α) (depth : ℕ) (side : Bool) (U : Finset α) : Finset α :=
  U.filter fun x => bits depth x = side

theorem bitPart_card_add (bits : MaskBits α) (depth : ℕ) (U : Finset α) :
    (bitPart bits depth false U).card + (bitPart bits depth true U).card = U.card := by
  have h := Finset.card_filter_add_card_filter_not (s := U)
    (p := fun x => bits depth x = false)
  simpa [bitPart, Bool.not_eq_false] using h

/-- Overflow count includes an overflowing full-prefix node that is dropped. -/
def overflowNodes (C : ℕ) (bits : MaskBits α) (depth : ℕ) : ℕ → Finset α → ℕ
  | 0, U => if C < U.card then 1 else 0
  | fuel + 1, U => if C < U.card then
      1 + overflowNodes C bits (depth + 1) fuel (bitPart bits depth false U) +
        overflowNodes C bits (depth + 1) fuel (bitPart bits depth true U)
    else 0

/-- The task count includes empty completed tasks and dropped full prefixes. -/
def prefixTasks (C : ℕ) (bits : MaskBits α) (depth : ℕ) : ℕ → Finset α → ℕ
  | 0, _ => 1
  | fuel + 1, U => if C < U.card then
      1 + prefixTasks C bits (depth + 1) fuel (bitPart bits depth false U) +
        prefixTasks C bits (depth + 1) fuel (bitPart bits depth true U)
    else 1

/-- Sum of the lengths of all completed right dictionaries. -/
def completedEntries (C : ℕ) (bits : MaskBits α) (depth : ℕ) : ℕ → Finset α → ℕ
  | 0, U => if C < U.card then 0 else U.card
  | fuel + 1, U => if C < U.card then
      completedEntries C bits (depth + 1) fuel (bitPart bits depth false U) +
        completedEntries C bits (depth + 1) fuel (bitPart bits depth true U)
    else U.card

/-- The sum of ambient entry counts over all task nodes, for charging by depth. -/
def potentialVisits (C : ℕ) (bits : MaskBits α) (depth : ℕ) : ℕ → Finset α → ℕ
  | 0, U => U.card
  | fuel + 1, U => if C < U.card then
      U.card + potentialVisits C bits (depth + 1) fuel (bitPart bits depth false U) +
        potentialVisits C bits (depth + 1) fuel (bitPart bits depth true U)
    else U.card

/-- Raw occurrences are a separate type and retain all multiplicities. Task
branching is decided by `U`, the distinct entries, rather than by `T`. -/
def rawVisits {β : Type*} (C : ℕ) (bits : MaskBits α) (rawBits : MaskBits β)
    (depth : ℕ) : ℕ → Finset α → Finset β → ℕ
  | 0, _, T => T.card
  | fuel + 1, U, T => if C < U.card then
      T.card + rawVisits C bits rawBits (depth + 1) fuel
          (bitPart bits depth false U) (bitPart rawBits depth false T) +
        rawVisits C bits rawBits (depth + 1) fuel
          (bitPart bits depth true U) (bitPart rawBits depth true T)
    else T.card

/-- The bucket reached by following a designated entry's complete prefix. -/
def fullPrefixBucket (bits : MaskBits α) (depth : ℕ) (e : α) : ℕ → Finset α → Finset α
  | 0, U => U
  | fuel + 1, U => fullPrefixBucket bits (depth + 1) e fuel
      (bitPart bits depth (bits depth e) U)

/-- The actual refinement path stops at the first dictionary that fits. -/
def reachesCompleted (C : ℕ) (bits : MaskBits α) (depth : ℕ) (e : α) :
    ℕ → Finset α → Prop
  | 0, U => U.card ≤ C
  | fuel + 1, U => U.card ≤ C ∨ reachesCompleted C bits (depth + 1) e fuel
      (bitPart bits depth (bits depth e) U)

theorem mem_fullPrefixBucket (bits : MaskBits α) (depth fuel : ℕ)
    {e : α} {U : Finset α} (he : e ∈ U) :
    e ∈ fullPrefixBucket bits depth e fuel U := by
  induction fuel generalizing depth U with
  | zero => exact he
  | succ fuel ih =>
    apply ih
    exact Finset.mem_filter.mpr ⟨he, rfl⟩

/-- A fitting full-prefix bucket ensures that the designated path completes,
even if larger ancestors overflow. -/
theorem reachesCompleted_of_fullPrefix_fits (C : ℕ) (bits : MaskBits α)
    (depth fuel : ℕ) (e : α) (U : Finset α)
    (hfit : (fullPrefixBucket bits depth e fuel U).card ≤ C) :
    reachesCompleted C bits depth e fuel U := by
  induction fuel generalizing depth U with
  | zero => exact hfit
  | succ fuel ih =>
    right
    exact ih (depth + 1) (bitPart bits depth (bits depth e) U) hfit

theorem overflowNodes_capacity_bound (C : ℕ) (bits : MaskBits α)
    (depth fuel : ℕ) (U : Finset α) :
    C * overflowNodes C bits depth fuel U ≤ (fuel + 1) * U.card := by
  induction fuel generalizing depth U with
  | zero =>
    simp only [overflowNodes]
    split_ifs with h <;> simp_all
    omega
  | succ fuel ih =>
    simp only [overflowNodes]
    split_ifs with h
    · have h0 := ih (depth + 1) (bitPart bits depth false U)
      have h1 := ih (depth + 1) (bitPart bits depth true U)
      have hc := bitPart_card_add bits depth U
      nlinarith
    · simp

theorem prefixTasks_le_overflowNodes (C : ℕ) (bits : MaskBits α)
    (depth fuel : ℕ) (U : Finset α) :
    prefixTasks C bits depth fuel U ≤ 1 + 2 * overflowNodes C bits depth fuel U := by
  induction fuel generalizing depth U with
  | zero => simp [prefixTasks, overflowNodes]
  | succ fuel ih =>
    simp only [prefixTasks, overflowNodes]
    split_ifs with h
    · have h0 := ih (depth + 1) (bitPart bits depth false U)
      have h1 := ih (depth + 1) (bitPart bits depth true U)
      omega
    · simp

/-- Division-free version of the right task-start bound. -/
theorem prefixTasks_capacity_bound (C : ℕ) (bits : MaskBits α)
    (depth fuel : ℕ) (U : Finset α) :
    C * prefixTasks C bits depth fuel U ≤ C + 2 * (fuel + 1) * U.card := by
  have ht := prefixTasks_le_overflowNodes C bits depth fuel U
  have ho := overflowNodes_capacity_bound C bits depth fuel U
  nlinarith

theorem completedEntries_le_card (C : ℕ) (bits : MaskBits α)
    (depth fuel : ℕ) (U : Finset α) :
    completedEntries C bits depth fuel U ≤ U.card := by
  induction fuel generalizing depth U with
  | zero => simp only [completedEntries]; split_ifs <;> omega
  | succ fuel ih =>
    simp only [completedEntries]
    split_ifs with h
    · have h0 := ih (depth + 1) (bitPart bits depth false U)
      have h1 := ih (depth + 1) (bitPart bits depth true U)
      have hc := bitPart_card_add bits depth U
      omega
    · rfl

/-- Every occurrence has exactly one prefix at a fixed depth. The total
potential work is charged by depth, even for occurrences later rejected. -/
theorem potentialVisits_le_depth_mul_card (C : ℕ) (bits : MaskBits α)
    (depth fuel : ℕ) (U : Finset α) :
    potentialVisits C bits depth fuel U ≤ (fuel + 1) * U.card := by
  induction fuel generalizing depth U with
  | zero => simp [potentialVisits]
  | succ fuel ih =>
    simp only [potentialVisits]
    split_ifs with h
    · have h0 := ih (depth + 1) (bitPart bits depth false U)
      have h1 := ih (depth + 1) (bitPart bits depth true U)
      have hc := bitPart_card_add bits depth U
      nlinarith
    · nlinarith

/-- The occurrence bound is independent of deduplication and validity tests. -/
theorem rawVisits_le_depth_mul_card {β : Type*}
    (C : ℕ) (bits : MaskBits α) (rawBits : MaskBits β)
    (depth fuel : ℕ) (U : Finset α) (T : Finset β) :
    rawVisits C bits rawBits depth fuel U T ≤ (fuel + 1) * T.card := by
  induction fuel generalizing depth U T with
  | zero => simp [rawVisits]
  | succ fuel ih =>
    simp only [rawVisits]
    split_ifs with h
    · have h0 := ih (depth + 1) (bitPart bits depth false U)
        (bitPart rawBits depth false T)
      have h1 := ih (depth + 1) (bitPart bits depth true U)
        (bitPart rawBits depth true T)
      have hc := bitPart_card_add rawBits depth T
      nlinarith
    · nlinarith

/-- Even charging the left array at every task bounds all actual final-check
inputs. This includes every reuse of the same retained left array. -/
theorem checkInputs_le (C L : ℕ) (hL : L ≤ C) (bits : MaskBits α)
    (depth fuel : ℕ) (U : Finset α) :
    completedEntries C bits depth fuel U + L * prefixTasks C bits depth fuel U ≤
      L + (2 * fuel + 3) * U.card := by
  have ht := prefixTasks_le_overflowNodes C bits depth fuel U
  have ho := overflowNodes_capacity_bound C bits depth fuel U
  have he := completedEntries_le_card C bits depth fuel U
  have hscale := Nat.mul_le_mul_left (overflowNodes C bits depth fuel U) hL
  nlinarith

end LowSpaceSubsetSum

end OAI
