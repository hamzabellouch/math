import OAI.MeasureTheory.DyadicAvoidance.WindowRecursion
import OAI.MeasureTheory.DyadicAvoidance.WindowPlacement

namespace OAI

namespace Problem310.WindowSpanSum

open WindowRecursion

/-- The window lengths in edge preorder; the first length is that of the
incoming edge, followed by its complete descendant block. -/
def preorderLengths (M g r₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | h + 1 => (List.replicate M
      (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h)).flatten

/-- Charge a gap after every entry, including the final entry. -/
def paddedSum (g : ℕ) (L : List ℕ) : ℕ := (L.map (fun r => r + g)).sum

@[simp] theorem paddedSum_nil (g : ℕ) : paddedSum g [] = 0 := rfl

@[simp] theorem paddedSum_cons (g r : ℕ) (L : List ℕ) :
    paddedSum g (r :: L) = r + g + paddedSum g L := rfl

@[simp] theorem paddedSum_append (g : ℕ) (L K : List ℕ) :
    paddedSum g (L ++ K) = paddedSum g L + paddedSum g K := by
  simp [paddedSum]

@[simp] theorem paddedSum_flatten_replicate (g M : ℕ) (L : List ℕ) :
    paddedSum g (List.replicate M L).flatten = M * paddedSum g L := by
  induction M with
  | zero => simp [paddedSum]
  | succ M ih =>
      simp only [List.replicate_succ, List.flatten_cons, paddedSum_append, ih]
      ring

private theorem last_gap (M g : ℕ) (hM : 1 ≤ M) : (M - 1) * g + g = M * g := by
  simpa [Nat.add_mul] using congrArg (fun n => n * g) (Nat.sub_add_cancel hM)

/-- The exact recursive span is the preorder padded sum with the final gap removed. -/
theorem paddedSum_preorderLengths (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (preorderLengths M g r₀ h) =
      if h = 0 then 0 else span M g r₀ h + g := by
  induction h with
  | zero => rfl
  | succ h ih =>
      rw [preorderLengths, paddedSum_flatten_replicate, paddedSum_cons, ih]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      rw [span_succ]
      have hg := last_gap M g hM
      cases h with
      | zero =>
          simp only [ite_true, childSpan_zero, Nat.add_zero, Nat.zero_add]
          nlinarith
      | succ h =>
          simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
          rw [childSpan_succ]
          nlinarith

/-- A child block has its precise geometric span plus one terminal gap. -/
theorem paddedSum_childBlock (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h) =
      childSpan M g r₀ h + g := by
  rw [paddedSum_cons, paddedSum_preorderLengths M g r₀ h hM]
  cases h with
  | zero => simp
  | succ h => simp [childSpan_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- This is exactly the padded-length budget consumed by `WindowPlacement.block_padding`. -/
theorem childBlock_budget (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h) ≤
      2 * WindowRecursion.length M g r₀ (h + 1) + g := by
  rw [paddedSum_childBlock M g r₀ h hM]
  exact Nat.add_le_add_right (childSpan_le_twice_length M g r₀ h) g

/-- Any consecutive rank slice having the child-block padded sum inherits padding.
The caller only needs to identify its rank slice with the child's preorder block. -/
theorem block_padding_of_child_sum {len : ℕ → ℕ} {g i m M r₀ h : ℕ}
    (hM : 1 ≤ M) (hlen : 0 < len (i + m))
    (hsum : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) =
      paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h)) :
    WindowPlacement.finish len g (i + m) - WindowPlacement.start len g i + 1 ≤
      2 * WindowRecursion.length M g r₀ (h + 1) := by
  apply WindowPlacement.block_padding hlen
  rw [hsum]
  exact childBlock_budget M g r₀ h hM

/-- The endpoint form needed by the concrete window metadata avoids natural
subtraction and needs no positivity premise on an arbitrary rank sequence. -/
theorem block_endpoint_bound_of_child_sum {len : ℕ → ℕ} {g i m M r₀ h : ℕ}
    (hM : 1 ≤ M)
    (hsum : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) =
      paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h)) :
    WindowPlacement.finish len g (i + m) + 1 ≤ WindowPlacement.start len g i +
      2 * WindowRecursion.length M g r₀ (h + 1) := by
  have heq := WindowPlacement.block_endpoint len g i m
  have hbudget := childBlock_budget M g r₀ h hM
  rw [← hsum] at hbudget
  omega

/-- Every serialized window retains the common threshold, including descendants. -/
theorem threshold_le_of_mem_preorderLengths (M g r₀ h : ℕ) :
    ∀ r ∈ preorderLengths M g r₀ h, r₀ ≤ r := by
  induction h with
  | zero => simp [preorderLengths]
  | succ h ih =>
      intro r hr
      simp only [preorderLengths, List.mem_flatten, List.mem_replicate] at hr
      obtain ⟨L, ⟨_, rfl⟩, hr⟩ := hr
      rcases List.mem_cons.mp hr with heq | hr
      · subst r
        exact WindowRecursion.threshold_le_length _ _ _ _
      · exact ih r hr

/-- No child block is empty: its incoming window is always the first entry. -/
theorem childBlock_ne_nil (M g r₀ h : ℕ) :
    WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h ≠ [] := by
  simp

/-- Positivity needed to turn padded rank sums into inclusive endpoint bounds. -/
theorem positive_of_mem_childBlock {M g r₀ h r : ℕ} (hr₀ : 0 < r₀)
    (hr : r ∈ WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h) :
    0 < r := by
  rcases List.mem_cons.mp hr with heq | hr
  · subst r
    exact WindowRecursion.length_pos _ _ _ _ hr₀
  · exact hr₀.trans_le (threshold_le_of_mem_preorderLengths _ _ _ _ r hr)

end Problem310.WindowSpanSum

end OAI
