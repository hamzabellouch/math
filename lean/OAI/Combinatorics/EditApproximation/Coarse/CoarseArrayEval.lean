import OAI.Combinatorics.EditApproximation.Coarse.CoarseTransforms
import OAI.Combinatorics.EditApproximation.Coarse.CoarseWork

namespace OAI

/-!
# Shared coarse array evaluation

A missing array is a constant-zero marker. An expanded child is evaluated
once, then transformed by the two linear sweeps, thresholded, and added
to its siblings. The instrumented counter charges rational arithmetic and
comparisons; allocation, source-width preprocessing and integer addressing
are separate parts of the machine implementation.
-/

namespace EditApproximation

open Finset MeasureTheory

universe u

/-- Stored cells have the complete shift-domain length; `none` is zero. -/
abbrev CoarseStoredArray (n : ℕ) := Option {cells : List ℚ // cells.length = n}

def coarseStoredRead {n : ℕ} (array : CoarseStoredArray n) (v : Fin n) : ℚ :=
  match array with
  | none => 0
  | some cells => cells.1[v.val]'(by rw [cells.2]; exact v.isLt)

def coarseStoredOfFn {n : ℕ} (value : Fin n → ℚ) : CoarseStoredArray n :=
  some ⟨List.ofFn value, List.length_ofFn⟩

theorem coarseStoredRead_ofFn {n : ℕ} (value : Fin n → ℚ) (v : Fin n) :
    coarseStoredRead (coarseStoredOfFn value) v = value v := by
  simp only [coarseStoredRead, coarseStoredOfFn, List.getElem_ofFn]

def coarseStoredMap {n : ℕ} (f : ℚ → ℚ) : CoarseStoredArray n → CoarseStoredArray n × ℕ
  | none => (none, 0)
  | some cells => (some ⟨cells.1.map f, by simp only [List.length_map, cells.2]⟩, 2 * n)

theorem coarseStoredMap_read {n : ℕ} (f : ℚ → ℚ) (hzero : f 0 = 0)
    (array : CoarseStoredArray n) (v : Fin n) :
    coarseStoredRead (coarseStoredMap f array).1 v = f (coarseStoredRead array v) := by
  cases array with
  | none => exact hzero.symm
  | some cells => simp only [coarseStoredMap, coarseStoredRead, List.getElem_map]

theorem coarseStoredMap_cost {n : ℕ} (f : ℚ → ℚ) (array : CoarseStoredArray n) :
    (coarseStoredMap f array).2 ≤ 2 * n := by
  cases array <;> simp only [coarseStoredMap] <;> omega

def coarseStoredAdd {n : ℕ} : CoarseStoredArray n → CoarseStoredArray n → CoarseStoredArray n × ℕ
  | none, right => (right, 0)
  | left, none => (left, 0)
  | some left, some right =>
    (some ⟨List.zipWith (· + ·) left.1 right.1,
      by simp only [List.length_zipWith, left.2, right.2, min_self]⟩, n)

theorem coarseStoredAdd_read {n : ℕ} (left right : CoarseStoredArray n) (v : Fin n) :
    coarseStoredRead (coarseStoredAdd left right).1 v =
      coarseStoredRead left v + coarseStoredRead right v := by
  cases left with
  | none => simp only [coarseStoredAdd, coarseStoredRead, zero_add]
  | some left =>
    cases right with
    | none => simp only [coarseStoredAdd, coarseStoredRead, add_zero]
    | some right => simp only [coarseStoredAdd, coarseStoredRead, List.getElem_zipWith]

theorem coarseStoredAdd_cost {n : ℕ} (left right : CoarseStoredArray n) :
    (coarseStoredAdd left right).2 ≤ n := by
  cases left <;> cases right <;> simp only [coarseStoredAdd] <;> omega

/-- The costed linear sweeps operate on the stored cells. -/
def coarseStoredPenalty {n : ℕ} : CoarseStoredArray n → CoarseStoredArray n × ℕ
  | none => (none, 0)
  | some cells =>
    let result := coarseCostedPenaltyTransform cells.1
    (some ⟨result.1, by rw [(coarseCostedPenaltyTransform_result cells.1).1,
      coarsePenaltyTransform_length, cells.2]⟩, result.2)

theorem coarseStoredPenalty_cost {n : ℕ} (array : CoarseStoredArray n) :
    (coarseStoredPenalty array).2 ≤ 5 * n := by
  cases array with
  | none => simp only [coarseStoredPenalty]; omega
  | some cells =>
    exact (coarseCostedPenaltyTransform_result cells.1).2.trans_eq (by rw [cells.2])

theorem coarseStoredPenalty_read {n : ℕ} [NeZero n]
    (array : CoarseStoredArray n) (v : Fin n) :
    coarseStoredRead (coarseStoredPenalty array).1 v =
      univ.inf' univ_nonempty (fun next =>
        coarseStoredRead array next + (2 * Nat.dist v.val next.val : ℕ)) := by
  cases array with
  | none =>
    simp only [coarseStoredPenalty, coarseStoredRead, zero_add]
    apply le_antisymm
    · apply le_inf'
      intro next hnext
      positivity
    · simpa only [Nat.dist_self, mul_zero, Nat.cast_zero] using
        inf'_le (fun next : Fin n => ((2 * Nat.dist v.val next.val : ℕ) : ℚ)) (mem_univ v)
  | some cells =>
    rcases cells with ⟨cells, hlength⟩
    subst n
    simp only [coarseStoredPenalty, coarseStoredRead,
      (coarseCostedPenaltyTransform_result cells).1]
    exact coarsePenaltyTransform_getElem cells v

/-- Each list member is evaluated once and its whole array is reused. -/
def coarseArrayEvalChildren {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (evaluate : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ →
      CoarseStoredArray (2 * k + 1) × ℕ) (allowance : ℚ) :
    List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D) → ℕ →
      CoarseStoredArray (2 * k + 1) × ℕ
  | [], _ => (none, 0)
  | (child, draw, below) :: rest, start =>
    let threshold := coarseChildThreshold B Q allowance draw
    let evaluated := evaluate child below (lam * threshold) start
    let penalty := coarseStoredPenalty evaluated.1
    let contribution := coarseStoredMap
      (coarseThresholdContribution threshold (allowance / Q)) penalty.1
    let remainder := coarseArrayEvalChildren k Q lam evaluate allowance rest
      (start + child.word.length)
    let total := coarseStoredAdd contribution.1 remainder.1
    (total.1, evaluated.2 + penalty.2 + contribution.2 + remainder.2 + total.2 + 7)

/-- Actual shared-array recursion. Pruning creates a zero marker and does
not traverse any descendants. -/
def coarseArrayEval {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α)) :
    {D : ℕ} → CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ →
      CoarseStoredArray (2 * k + 1) × ℕ
  | _, tree, draws, allowance, start =>
    if (tree.word.length : ℚ) ≤ allowance then (none, 1) else
    match tree, draws with
    | .leaf letter, _ =>
      (coarseStoredOfFn (fun shift =>
        (coarseShiftCost k frame (.leaf (B := B) letter) start shift : ℚ)),
        1 + 3 * (2 * k + 1))
    | .branch children, (draws, below) =>
      let result := coarseArrayEvalChildren k Q lam
        (fun child => coarseArrayEval k Q lam frame child) allowance
        (List.ofFn fun i => (children i, draws i, below i)) start
      (result.1, result.2 + 1)

theorem coarseArrayEvalChildren_read {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (evaluate : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ →
      CoarseStoredArray (2 * k + 1) × ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (hchild : ∀ child draw below, (child, draw, below) ∈ children →
      ∀ a start shift, 0 < a → coarseStoredRead (evaluate child below a start).1 shift =
        value child below a start shift)
    (allowance : ℚ) (start : ℕ) (shift : Fin (2 * k + 1))
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    coarseStoredRead (coarseArrayEvalChildren k Q lam evaluate allowance children start).1 shift =
      coarseThresholdChildrenCost k Q lam value allowance children start shift := by
  induction children generalizing start with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have ht : 0 < coarseChildThreshold B Q allowance draw := coarseChildThreshold_pos draw hQ ha
    have hc := hchild child draw below (by simp)
    have hrest := ih (fun child draw below hmem => hchild child draw below (by simp [hmem]))
      (start + child.word.length)
    simp only [coarseArrayEvalChildren, coarseThresholdChildrenCost]
    rw [coarseStoredAdd_read, coarseStoredMap_read]
    · rw [coarseStoredPenalty_read, hrest]
      congr 2
      apply congrArg
      funext next
      rw [hc _ start next (mul_pos hlam ht)]
    · simp only [coarseThresholdContribution, not_le_of_gt ht, ↓reduceIte]

theorem coarseArrayEval_read {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (draws : CoarseThresholdDraws B D)
    (allowance : ℚ) (start : ℕ) (shift : Fin (2 * k + 1))
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    coarseStoredRead (coarseArrayEval k Q lam frame tree draws allowance start).1 shift =
      coarseThresholdEstimate k Q lam frame tree draws allowance start shift := by
  induction tree generalizing allowance start shift with
  | leaf letter =>
    simp only [coarseArrayEval, coarseThresholdEstimate]
    split_ifs
    · rfl
    · exact coarseStoredRead_ofFn _ shift
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseArrayEval, coarseThresholdEstimate]
    split_ifs
    · rfl
    · apply coarseArrayEvalChildren_read k Q lam _ _ _ _ allowance start shift hQ hlam ha
      intro child draw below hmem a start shift ha
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
      cases hi
      exact ih i _ a start shift ha

/-- The instrumented child traversal charges the once-evaluated child plus
at most sixteen parent shift-array units for each list member. -/
theorem coarseArrayEvalChildren_cost {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (evaluate : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ →
      CoarseStoredArray (2 * k + 1) × ℕ)
    (work : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (hchild : ∀ child draw below, (child, draw, below) ∈ children →
      ∀ a start, (evaluate child below a start).2 ≤ 32 * work child below a + 1)
    (allowance : ℚ) (start : ℕ) :
    (coarseArrayEvalChildren k Q lam evaluate allowance children start).2 ≤
      32 * coarseActiveChildrenWork Q lam allowance work children +
        16 * children.length * (2 * k + 1) := by
  induction children generalizing start with
  | nil => simp only [coarseArrayEvalChildren, coarseActiveChildrenWork, List.length_nil,
      mul_zero, zero_mul, zero_add, le_refl]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hc := hchild child draw below (by simp)
      (lam * coarseChildThreshold B Q allowance draw) start
    have hr := ih (fun child draw below hmem => hchild child draw below (by simp [hmem]))
      (start + child.word.length)
    have hp := coarseStoredPenalty_cost
      (evaluate child below (lam * coarseChildThreshold B Q allowance draw) start).1
    have hm := coarseStoredMap_cost
      (coarseThresholdContribution (coarseChildThreshold B Q allowance draw) (allowance / Q))
      (coarseStoredPenalty (evaluate child below (lam * coarseChildThreshold B Q allowance draw) start).1).1
    have hs := coarseStoredAdd_cost
      (coarseStoredMap (coarseThresholdContribution (coarseChildThreshold B Q allowance draw) (allowance / Q))
        (coarseStoredPenalty (evaluate child below (lam * coarseChildThreshold B Q allowance draw) start).1).1).1
      (coarseArrayEvalChildren k Q lam evaluate allowance rest (start + child.word.length)).1
    simp only [coarseArrayEvalChildren, coarseActiveChildrenWork, List.length_cons]
    nlinarith

/-- Every execution's shared evaluation has the rational-operation cost
bounded by the very same pruning-stopped counter used in expectation. -/
theorem coarseArrayEval_cost {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (draws : CoarseThresholdDraws B D)
    (allowance : ℚ) (start : ℕ) :
    (coarseArrayEval k Q lam frame tree draws allowance start).2 ≤
      32 * coarseActiveArrayWork k Q lam tree draws allowance + 1 := by
  have hB : 1 ≤ B := Nat.pos_of_ne_zero (NeZero.ne B)
  induction tree generalizing allowance start with
  | leaf letter =>
    simp only [coarseArrayEval, coarseActiveArrayWork]
    split_ifs
    · omega
    · nlinarith
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseArrayEval, coarseActiveArrayWork]
    split_ifs
    · omega
    · have hc := coarseArrayEvalChildren_cost k Q lam
        (fun child => coarseArrayEval k Q lam frame child)
        (fun child => coarseActiveArrayWork k Q lam child)
        (List.ofFn fun i => (children i, draws i, below i))
        (by
          intro child draw below hmem a start
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i _ a start)
        allowance start
      simp only [List.length_ofFn] at hc
      nlinarith

/-- Expected rational-operation count for the actual shared-array evaluator.
This estimate holds on every execution, including inaccurate ones. -/
theorem coarseArrayEval_expected_bound {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (allowance : ℚ) (start : ℕ)
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    (∫ draws, ((coarseArrayEval k Q lam frame tree draws allowance start).2 : ℝ)
      ∂coarseDrawMeasure B D) ≤
      32 * ((B * (2 * k + 1) : ℕ) * (tree.word.length : ℝ) / allowance *
        coarseWorkMultiplier (coarseInverseAllowanceFactor B Q lam) D) + 1 := by
  calc
    _ ≤ ∫ draws, 32 * (coarseActiveArrayWork k Q lam tree draws allowance : ℝ) + 1
        ∂coarseDrawMeasure B D := by
      apply MeasureTheory.integral_mono (.of_finite) (.of_finite)
      intro draws
      dsimp only
      exact_mod_cast coarseArrayEval_cost k Q lam frame tree draws allowance start
    _ = 32 * (∫ draws, (coarseActiveArrayWork k Q lam tree draws allowance : ℝ)
        ∂coarseDrawMeasure B D) + 1 := by
      rw [MeasureTheory.integral_add (.of_finite) (.of_finite),
        MeasureTheory.integral_const_mul]
      simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ,
        smul_eq_mul, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (coarseActiveArrayWork_expected_bound k Q lam tree allowance hQ hlam ha) (by norm_num)) le_rfl

end EditApproximation

end OAI
