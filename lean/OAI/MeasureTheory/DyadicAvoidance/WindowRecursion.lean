import Mathlib

namespace OAI

namespace Problem310.WindowRecursion

/-- Total span occupied by the windows in a complete tree of the given height.
At a bottom-level child there is no following subtree gap; at higher levels the
incoming window is followed by one gap and the complete child subtree. -/
def span (M g r₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 =>
      M * (max r₀ (g + span M g r₀ h) +
        if h = 0 then 0 else g + span M g r₀ h) + (M - 1) * g

/-- Length of an incoming window whose parent has height `h + 1`.
The value at height zero is unused and is set equal to the threshold. -/
def length (M g r₀ : ℕ) : ℕ → ℕ
  | 0 => r₀
  | h + 1 => max r₀ (g + span M g r₀ h)

/-- Span of one incoming-edge window and the subtree beneath that edge. -/
def childSpan (M g r₀ h : ℕ) : ℕ :=
  length M g r₀ (h + 1) + if h = 0 then 0 else g + span M g r₀ h

@[simp] theorem span_zero (M g r₀ : ℕ) : span M g r₀ 0 = 0 := rfl

@[simp] theorem length_zero (M g r₀ : ℕ) : length M g r₀ 0 = r₀ := rfl

@[simp] theorem length_succ (M g r₀ h : ℕ) :
    length M g r₀ (h + 1) = max r₀ (g + span M g r₀ h) := rfl

theorem span_succ (M g r₀ h : ℕ) :
    span M g r₀ (h + 1) = M * childSpan M g r₀ h + (M - 1) * g := rfl

@[simp] theorem childSpan_zero (M g r₀ : ℕ) :
    childSpan M g r₀ 0 = length M g r₀ 1 := by
  simp [childSpan]

@[simp] theorem span_one (M g r₀ : ℕ) :
    span M g r₀ 1 = M * length M g r₀ 1 + (M - 1) * g := by
  rw [span_succ, childSpan_zero]

theorem childSpan_succ (M g r₀ h : ℕ) :
    childSpan M g r₀ (h + 1) =
      length M g r₀ (h + 2) + g + span M g r₀ (h + 1) := by
  simp [childSpan, Nat.add_assoc]

theorem span_succ_succ (M g r₀ h : ℕ) :
    span M g r₀ (h + 2) =
      M * (length M g r₀ (h + 2) + g + span M g r₀ (h + 1)) + (M - 1) * g := by
  rw [show h + 2 = (h + 1) + 1 by omega, span_succ, childSpan_succ]

theorem threshold_le_length (M g r₀ h : ℕ) : r₀ ≤ length M g r₀ h := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact le_max_left _ _

theorem gap_add_span_le_length (M g r₀ h : ℕ) :
    g + span M g r₀ h ≤ length M g r₀ (h + 1) := le_max_right _ _

theorem length_pos (M g r₀ h : ℕ) (hr₀ : 0 < r₀) :
    0 < length M g r₀ h := hr₀.trans_le (threshold_le_length _ _ _ _)

theorem length_le_childSpan (M g r₀ h : ℕ) :
    length M g r₀ (h + 1) ≤ childSpan M g r₀ h := Nat.le_add_right _ _

/-- The key padding estimate: an entire child block occupies no more than twice
its incoming window length, independently of the size of the complete tree. -/
theorem childSpan_le_twice_length (M g r₀ h : ℕ) :
    childSpan M g r₀ h ≤ 2 * length M g r₀ (h + 1) := by
  have hp := gap_add_span_le_length M g r₀ h
  dsimp [childSpan]
  split_ifs <;> omega

theorem childSpan_pos (M g r₀ h : ℕ) (hr₀ : 0 < r₀) :
    0 < childSpan M g r₀ h :=
  (length_pos M g r₀ (h + 1) hr₀).trans_le (length_le_childSpan _ _ _ _)

theorem childSpan_le_span (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    childSpan M g r₀ h ≤ span M g r₀ (h + 1) := by
  rw [span_succ]
  calc
    childSpan M g r₀ h ≤ M * childSpan M g r₀ h := by
      simpa using Nat.mul_le_mul_right (childSpan M g r₀ h) hM
    _ ≤ _ := Nat.le_add_right _ _

theorem span_pos (M g r₀ h : ℕ) (hM : 1 ≤ M) (hr₀ : 0 < r₀) :
    0 < span M g r₀ (h + 1) :=
  (childSpan_pos M g r₀ h hr₀).trans_le (childSpan_le_span M g r₀ h hM)

theorem span_le_length_succ (M g r₀ h : ℕ) :
    span M g r₀ h ≤ length M g r₀ (h + 1) := by
  exact (Nat.le_add_left _ _).trans (gap_add_span_le_length _ _ _ _)

theorem span_le_span_succ (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    span M g r₀ h ≤ span M g r₀ (h + 1) :=
  (span_le_length_succ M g r₀ h).trans
    ((length_le_childSpan M g r₀ h).trans (childSpan_le_span M g r₀ h hM))

theorem monotone_span (M g r₀ : ℕ) (hM : 1 ≤ M) : Monotone (span M g r₀) :=
  monotone_nat_of_le_succ (fun h => span_le_span_succ M g r₀ h hM)

theorem monotone_length (M g r₀ : ℕ) (hM : 1 ≤ M) : Monotone (length M g r₀) := by
  apply monotone_nat_of_le_succ
  intro h
  cases h with
  | zero => exact threshold_le_length _ _ _ _
  | succ h =>
    exact max_le_max le_rfl (Nat.add_le_add_left (span_le_span_succ M g r₀ h hM) g)

end Problem310.WindowRecursion

end OAI
