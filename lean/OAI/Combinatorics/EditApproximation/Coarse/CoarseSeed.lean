import OAI.Combinatorics.EditApproximation.Geometry.Connections
import OAI.Combinatorics.EditApproximation.Geometry.AlignmentSplitting
import OAI.Combinatorics.EditApproximation.Geometry.Leaves
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The actual bounded-shift coarse tree

Section 3's deterministic shift representation uses a complete finite
branching tree with empty/singleton source leaves. Bounded integer shifts
are encoded by `Fin (2k+1)`; code `k` is shift zero. Virtual target positions
are represented by fresh `none` symbols in a finite surrounding frame.
-/

namespace EditApproximation

open Finset EditDistortion

universe u



namespace CoarseSourceTree



end CoarseSourceTree

/- Finite virtual frame, wide enough for every permitted shift. -/


/- Node values are the literal finite minima in the manuscript's
recurrence, with every child visited at its actual source start. -/




/-- The zero root shift is the middle integer code. -/


def coarseTreeValue {B D : ℕ} {α : Type u} [DecidableEq α]
    (tree : CoarseSourceTree B α D) (target : List α) (k : ℕ) : ℕ :=
  coarseShiftCost k (coarseTargetFrame k target) tree 0 (coarseRootShift k)

theorem substring_split {α : Type u} (word : List α) (lo mid hi : ℕ)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) :
    substring word lo hi = substring word lo mid ++ substring word mid hi := by
  have hindex : lo + (mid - lo) = mid := by omega
  calc
    _ = ((substring word lo hi).take (mid - lo)) ++
        ((substring word lo hi).drop (mid - lo)) := (List.take_append_drop _ _).symm
    _ = _ := by
      simp only [substring, List.take_drop, List.take_take, List.drop_drop, hindex,
        Nat.min_eq_left hhi]

theorem substring_one {α : Type u} (word : List α) (position : ℕ) :
    substring word position (position + 1) = word[position]?.toList := by
  rw [substring, ← List.take_drop, List.take_one, List.head?_drop]

/-- Leaf editing costs are at most the literal mismatch/virtual-position
value, including positions outside the finite frame. -/
theorem coarse_leaf_edit_le {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (frame : List (Option α)) (letter : Option α) (start : ℕ)
    (shift : Fin (2 * k + 1)) :
    edit ((CoarseSourceTree.leaf (B := B) letter).word.map some)
      (substring frame (start + shift.val)
        (start + shift.val + (CoarseSourceTree.leaf (B := B) letter).word.length)) ≤
      coarseShiftCost k frame (.leaf (B := B) letter) start shift := by
  cases letter with
  | none =>
    simp only [CoarseSourceTree.word, Option.toList_none, List.map_nil, List.length_nil,
      add_zero, coarseShiftCost, substring, List.drop_take_self]
    exact (cost_refl []).le
  | some letter =>
    simp only [CoarseSourceTree.word, Option.toList_some, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, zero_add, coarseShiftCost]
    rw [substring_one]
    cases hentry : frame[start + shift.val]? with
    | none =>
      simp only [Option.toList_none, Option.getD_none, reduceCtorEq, ↓reduceIte]
      exact (edit_le_max_length [some letter] []).trans (by simp)
    | some entry =>
      simp only [Option.toList_some, Option.getD_some]
      split_ifs with hequal
      · subst entry
        exact (cost_refl [some letter]).le
      · exact (edit_le_max_length [some letter] [entry]).trans (by simp)

/-- Moving both endpoints by a shift change costs at most twice the
absolute difference of their bounded integer codes. -/
theorem coarse_child_shift_edit_le {α : Type u} (frame : List α) (source : List α)
    (start shift next : ℕ) :
    edit source (substring frame (start + shift) (start + shift + source.length)) ≤
      edit source (substring frame (start + next) (start + next + source.length)) +
        2 * Nat.dist shift next := by
  have hmove := edit_substring_endpoints_le frame
    (start + next) (start + next + source.length)
    (start + shift) (start + shift + source.length)
  have hstart : Nat.dist (start + next) (start + shift) = Nat.dist shift next := by
    rw [Nat.dist_add_add_left, Nat.dist_comm]
  have hfinish : Nat.dist (start + next + source.length) (start + shift + source.length) =
      Nat.dist shift next := by rw [Nat.dist_add_add_right, hstart]
  rw [hstart, hfinish] at hmove
  have htriangle := cost_triangle (s := true) source
    (substring frame (start + next) (start + next + source.length))
    (substring frame (start + shift) (start + shift + source.length))
  change edit source (substring frame (start + shift) (start + shift + source.length)) ≤
    edit source (substring frame (start + next) (start + next + source.length)) +
      edit (substring frame (start + next) (start + next + source.length))
        (substring frame (start + shift) (start + shift + source.length)) at htriangle
  exact htriangle.trans (by omega)

/-- Actual child editing and endpoint movement give the recurrence's
lower invariant, proved directly on concatenated source strings. -/
theorem coarseChildrenCost_edit_lower {B D : ℕ} {α : Type u}
    (k : ℕ) (frame : List (Option α))
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D))
    (hchild : ∀ child ∈ children, ∀ start shift,
      edit (child.word.map some)
        (substring frame (start + shift.val) (start + shift.val + child.word.length)) ≤
          value child start shift) (start : ℕ) (shift : Fin (2 * k + 1)) :
    edit ((children.map CoarseSourceTree.word).flatten.map some)
      (substring frame (start + shift.val)
        (start + shift.val + (children.map CoarseSourceTree.word).flatten.length)) ≤
      coarseChildrenCost k value children start shift := by
  induction children generalizing start with
  | nil =>
    simp only [List.map_nil, List.flatten_nil, List.length_nil, add_zero, substring,
      List.drop_take_self, coarseChildrenCost]
    exact (cost_refl []).le
  | cons child rest ih =>
    have hfirst : edit (child.word.map some)
        (substring frame (start + shift.val) (start + shift.val + child.word.length)) ≤
      univ.inf' univ_nonempty (fun next => value child start next + 2 * Nat.dist shift.val next.val) := by
      apply le_inf'
      intro next hnext
      have hmove := coarse_child_shift_edit_le frame (child.word.map some) start shift.val next.val
      simp only [List.length_map] at hmove
      exact hmove.trans (Nat.add_le_add_right (hchild child (by simp) start next) _)
    have hrest := ih (fun next hnext => hchild next (by simp [hnext]))
      (start + child.word.length)
    have hsplit := substring_split frame (start + shift.val)
      (start + shift.val + child.word.length)
      (start + shift.val + (child.word ++ (rest.map CoarseSourceTree.word).flatten).length)
      (by omega) (by simp only [List.length_append]; omega)
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.length_append,
      coarseChildrenCost]
    simp only [List.length_append] at hsplit
    rw [hsplit]
    have happend := cost_append_le (s := true) (child.word.map some)
      (substring frame (start + shift.val) (start + shift.val + child.word.length))
      ((rest.map CoarseSourceTree.word).flatten.map some)
      (substring frame (start + shift.val + child.word.length)
        (start + shift.val + child.word.length + (rest.map CoarseSourceTree.word).flatten.length))
    have hrest' : edit ((rest.map CoarseSourceTree.word).flatten.map some)
        (substring frame (start + shift.val + child.word.length)
          (start + shift.val + child.word.length + (rest.map CoarseSourceTree.word).flatten.length)) ≤
        coarseChildrenCost k value rest (start + child.word.length) shift := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest
    have hresult := happend.trans (Nat.add_le_add hfirst hrest')
    change edit _ _ ≤ _ at hresult
    simpa only [Nat.add_assoc] using hresult

/-- The literal bounded-shift tree always dominates edit distance to its
corresponding shifted equal-width target interval. -/
theorem coarseShiftCost_edit_lower {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    edit (tree.word.map some)
      (substring frame (start + shift.val) (start + shift.val + tree.word.length)) ≤
      coarseShiftCost k frame tree start shift := by
  induction tree generalizing start shift with
  | leaf letter => exact coarse_leaf_edit_le k frame letter start shift
  | branch children ih =>
    simp only [CoarseSourceTree.word, coarseShiftCost]
    have hword : (List.ofFn children).map CoarseSourceTree.word =
        List.ofFn (fun i => (children i).word) := by
      simp only [List.map_ofFn, Function.comp_def]
    rw [← hword]
    apply coarseChildrenCost_edit_lower k frame
      (fun child => coarseShiftCost k frame child) (List.ofFn children)
    intro child hchild start shift
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchild
    exact ih i start shift

/-- The central equal-width target interval excludes all virtual symbols. -/
theorem coarseTargetFrame_center {α : Type u} (k : ℕ) (target : List α) :
    substring (coarseTargetFrame k target) k (k + target.length) = target.map some := by
  have hprefix : (List.replicate k (none : Option α) ++ target.map some).length = k + target.length := by simp
  rw [substring, coarseTargetFrame, ← hprefix, List.take_append_length]
  simpa only [List.length_replicate] using
    (List.drop_append_length (l₁ := List.replicate k (none : Option α)) (l₂ := target.map some))

/-- First deterministic shift-tree distortion inequality, for the actual
unrestricted unit-cost edit distance and actual finite recurrence. -/
theorem coarseTreeValue_edit_lower {B D : ℕ} {α : Type u} [DecidableEq α] [Inhabited α]
    (tree : CoarseSourceTree B α D) (target : List α) (k : ℕ)
    (hlength : tree.word.length = target.length) :
    edit tree.word target ≤ coarseTreeValue tree target k := by
  have h := coarseShiftCost_edit_lower k (coarseTargetFrame k target) tree 0 (coarseRootShift k)
  simp only [coarseRootShift, zero_add, hlength, coarseTargetFrame_center] at h
  have hmap := cost_map_eq_of_leftInverse (s := true) some
    (fun entry : Option α => entry.getD default) (by intro letter; rfl) tree.word target
  change edit (tree.word.map some) (target.map some) = edit tree.word target at hmap
  rw [hmap] at h
  exact h

theorem coarseChildrenCost_le_width {B D : ℕ} {α : Type u} (k : ℕ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D))
    (hchild : ∀ child ∈ children, ∀ start shift, value child start shift ≤ child.word.length)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseChildrenCost k value children start shift ≤ (children.map CoarseSourceTree.word).flatten.length := by
  induction children generalizing start with
  | nil => simp [coarseChildrenCost]
  | cons child rest ih =>
    have hmin := inf'_le (fun next => value child start next + 2 * Nat.dist shift.val next.val)
      (mem_univ shift)
    simp only [Nat.dist_self, mul_zero, add_zero] at hmin
    have hfirst := hchild child (by simp) start shift
    have hrest := ih (fun next hnext => hchild next (by simp [hnext]))
      (start + child.word.length)
    simp only [coarseChildrenCost, List.map_cons, List.flatten_cons, List.length_append]
    omega

/-- Constant shifts give the exact node-width bound used by pruning. -/
theorem coarseShiftCost_le_width {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseShiftCost k frame tree start shift ≤ tree.word.length := by
  induction tree generalizing start shift with
  | leaf letter =>
    cases letter with
    | none => simp [coarseShiftCost, CoarseSourceTree.word]
    | some letter =>
      simp only [coarseShiftCost, CoarseSourceTree.word, Option.toList_some,
        List.length_cons, List.length_nil]
      split_ifs <;> omega
  | branch children ih =>
    simp only [CoarseSourceTree.word, coarseShiftCost]
    have hword : (List.ofFn children).map CoarseSourceTree.word =
        List.ofFn (fun i => (children i).word) := by
      simp only [List.map_ofFn, Function.comp_def]
    rw [← hword]
    apply coarseChildrenCost_le_width k (fun child => coarseShiftCost k frame child) (List.ofFn children)
    intro child hchild start shift
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchild
    exact ih i start shift

/-- The literal consecutive capacity chunks cover exactly the permitted
before; zero capacity and empty trailing chunks are included. -/
theorem coarse_capacity_chunks {α : Type u} (source : List α) (B capacity : ℕ) :
    (List.ofFn fun i : Fin B => (source.drop (i.val * capacity)).take capacity).flatten =
      source.take (B * capacity) := by
  induction B generalizing source with
  | zero => simp
  | succ B ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, zero_mul, List.drop_zero, Fin.val_succ]
    have hchunks : (List.ofFn fun i : Fin B =>
        (source.drop ((i.val + 1) * capacity)).take capacity) =
        List.ofFn (fun i : Fin B => ((source.drop capacity).drop (i.val * capacity)).take capacity) := by
      congr 1
      funext i
      simp only [List.drop_drop, Nat.add_mul, one_mul, Nat.add_comm]
    rw [hchunks, ih, ← List.take_add]
    simp only [Nat.succ_mul, Nat.add_comm]

/-- A concrete complete source tree with empty/singleton leaves. Its
recursive child chunks have the capacity prescribed by the remaining depth. -/


theorem coarseSourceTreeOfList_word {α : Type u} (B D : ℕ) (source : List α) :
    (coarseSourceTreeOfList B D source).word = source.take (B ^ D) := by
  induction D generalizing source with
  | zero => simp only [coarseSourceTreeOfList, CoarseSourceTree.word, pow_zero, List.take_one]
  | succ D ih =>
    simp only [coarseSourceTreeOfList, CoarseSourceTree.word, ih, List.take_take, min_self]
    rw [coarse_capacity_chunks, pow_succ, Nat.mul_comm]

theorem coarseSourceTreeOfList_word_eq {α : Type u} (B D : ℕ) (source : List α)
    (hcapacity : source.length ≤ B ^ D) :
    (coarseSourceTreeOfList B D source).word = source := by
  rw [coarseSourceTreeOfList_word, List.take_of_length_le hcapacity]

/-- A real target character is present at its framed before index. -/
theorem coarseTargetFrame_prefix_get {α : Type u} (k : ℕ)
    (before suffix : List α) (letter : α) :
    (coarseTargetFrame k (before ++ letter :: suffix))[k + before.length]?.getD none = some letter := by
  rw [coarseTargetFrame, List.getElem?_append_left (by simp)]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left, List.getElem?_map]
  rw [List.getElem?_append_right (by omega)]
  simp

/-- Advancing an actual alignment cut gives a legal bounded shift. The
only budget is its preceding displacement plus its remaining edit cost. -/
theorem coarse_anchor_advance (k start before : ℕ) (shift : Fin (2 * k + 1))
    (sourceWidth targetWidth cutCost remaining : ℕ)
    (hanchor : start + shift.val = k + before)
    (hbudget : Nat.dist start before + (cutCost + remaining) ≤ k)
    (hsource : sourceWidth ≤ targetWidth + cutCost)
    (htarget : targetWidth ≤ sourceWidth + cutCost) :
    ∃ next : Fin (2 * k + 1),
      start + sourceWidth + next.val = k + (before + targetWidth) ∧
      Nat.dist shift.val next.val ≤ cutCost ∧
      Nat.dist (start + sourceWidth) (before + targetWidth) + remaining ≤ k := by
  let code := k + (before + targetWidth) - (start + sourceWidth)
  have hcode : code < 2 * k + 1 := by
    dsimp [code]
    simp only [Nat.dist] at hbudget
    omega
  refine ⟨⟨code, hcode⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [Nat.dist, code] at *
    omega

/-- Exact first-child alignment cost controls every actual shift-tree
leaf; no leaf correspondence oracle is assumed. -/
theorem coarse_leaf_edit_upper {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (target before piece suffix : List α) (letter : Option α)
    (start : ℕ) (shift : Fin (2 * k + 1))
    (htarget : target = before ++ piece ++ suffix)
    (hanchor : start + shift.val = k + before.length) :
    coarseShiftCost k (coarseTargetFrame k target) (.leaf (B := B) letter) start shift ≤
      edit (CoarseSourceTree.leaf (B := B) letter).word piece := by
  cases letter with
  | none => simp only [coarseShiftCost]; exact Nat.zero_le _
  | some letter =>
    by_cases hzero : edit [letter] piece = 0
    · have heq : [letter] = piece := (cost_eq_zero_iff (s := true)).mp hzero
      rw [← heq] at htarget
      subst target
      simp only [List.append_assoc, List.singleton_append, coarseShiftCost, hanchor,
        coarseTargetFrame_prefix_get, ↓reduceIte]
      exact Nat.zero_le _
    · have hpositive : 1 ≤ edit [letter] piece := by omega
      simp only [coarseShiftCost, CoarseSourceTree.word, Option.toList_some]
      split_ifs <;> omega

/-- Recursive actual optimal cuts bound child minima. The explicit
before allowance accounts for the displacement from the parent's shift. -/
theorem coarseChildrenCost_edit_upper {B D : ℕ} {α : Type u}
    (k : ℕ) (target : List α) (C : ℕ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D))
    (hchild : ∀ child ∈ children, ∀ (before piece suffix : List α) start shift,
      target = before ++ piece ++ suffix →
      start + shift.val = k + before.length →
      Nat.dist start before.length + edit child.word piece ≤ k →
      value child start shift ≤ C * edit child.word piece)
    (before piece suffix : List α) (start : ℕ)
    (parent anchor : Fin (2 * k + 1)) (allowance : ℕ)
    (htarget : target = before ++ piece ++ suffix)
    (hanchor : start + anchor.val = k + before.length)
    (hbudget : Nat.dist start before.length +
      edit (children.map CoarseSourceTree.word).flatten piece ≤ k)
    (hallowance : Nat.dist parent.val anchor.val ≤ allowance) :
    coarseChildrenCost k value children start parent ≤
      C * edit (children.map CoarseSourceTree.word).flatten piece +
        2 * children.length * (allowance + edit (children.map CoarseSourceTree.word).flatten piece) := by
  induction children generalizing before piece suffix start anchor allowance with
  | nil => simp only [coarseChildrenCost, List.length_nil, mul_zero, zero_mul, add_zero]; exact Nat.zero_le _
  | cons child rest ih =>
    obtain ⟨left, right, hlocal, hsplit⟩ := edit_append_split child.word
      (rest.map CoarseSourceTree.word).flatten piece
    have hsplit' : edit ((child :: rest).map CoarseSourceTree.word).flatten piece =
        edit child.word left + edit (rest.map CoarseSourceTree.word).flatten right := by
      simpa only [List.map_cons, List.flatten_cons] using hsplit
    have hfirst := hchild child (by simp) before left (right ++ suffix) start anchor
      (by simpa only [hlocal, List.append_assoc] using htarget) hanchor
      (by rw [hsplit'] at hbudget; omega)
    obtain ⟨hsource, htargetWidth⟩ := cost_length_bounds (s := true) child.word left
    change child.word.length ≤ left.length + edit child.word left at hsource
    change left.length ≤ child.word.length + edit child.word left at htargetWidth
    obtain ⟨next, hnext, hmove, hremaining⟩ := coarse_anchor_advance k start before.length anchor
      child.word.length left.length (edit child.word left)
      (edit (rest.map CoarseSourceTree.word).flatten right) hanchor
      (by simpa only [hsplit'] using hbudget) hsource htargetWidth
    have hnextAllowance : Nat.dist parent.val next.val ≤ allowance + edit child.word left :=
      (Nat.dist.triangle_inequality parent.val anchor.val next.val).trans
        (Nat.add_le_add hallowance hmove)
    have hrest := ih (fun next hnext => hchild next (by simp [hnext]))
      (before ++ left) right suffix (start + child.word.length) next
      (allowance + edit child.word left)
      (by simpa only [hlocal, List.append_assoc] using htarget)
      (by simpa only [List.length_append] using hnext)
      (by simpa only [List.length_append] using hremaining) hnextAllowance
    have hminimum := inf'_le (fun next => value child start next + 2 * Nat.dist parent.val next.val)
      (mem_univ anchor)
    have hfirstBound : univ.inf' univ_nonempty
        (fun next => value child start next + 2 * Nat.dist parent.val next.val) ≤
        C * edit child.word left + 2 * allowance :=
      hminimum.trans (Nat.add_le_add hfirst (Nat.mul_le_mul_left 2 hallowance))
    simp only [coarseChildrenCost, List.length_cons, hsplit']
    have hsum := Nat.add_le_add hfirstBound hrest
    nlinarith

/-- The actual bounded-shift recurrence is at most the manuscript's
linear-in-depth distortion, using optimal unrestricted edit scripts. -/
theorem coarseShiftCost_edit_upper {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (target : List α) (tree : CoarseSourceTree B α D)
    (before piece suffix : List α) (start : ℕ) (shift : Fin (2 * k + 1))
    (htarget : target = before ++ piece ++ suffix)
    (hanchor : start + shift.val = k + before.length)
    (hbudget : Nat.dist start before.length + edit tree.word piece ≤ k) :
    coarseShiftCost k (coarseTargetFrame k target) tree start shift ≤
      (1 + 2 * B * D) * edit tree.word piece := by
  induction tree generalizing before piece suffix start shift with
  | leaf letter =>
    simpa only [mul_zero, add_zero, one_mul] using
      coarse_leaf_edit_upper k target before piece suffix letter start shift htarget hanchor
  | @branch D children ih =>
    have hword : (List.ofFn children).map CoarseSourceTree.word =
        List.ofFn (fun i => (children i).word) := by
      simp only [List.map_ofFn, Function.comp_def]
    have hbound := coarseChildrenCost_edit_upper k target (1 + 2 * B * D)
      (fun child => coarseShiftCost k (coarseTargetFrame k target) child) (List.ofFn children)
      (by
        intro child hchild before piece suffix start shift htarget hanchor hbudget
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchild
        exact ih i before piece suffix start shift htarget hanchor hbudget)
      before piece suffix start shift shift 0 htarget hanchor
      (by simpa only [hword, CoarseSourceTree.word] using hbudget) (by simp)
    simp only [CoarseSourceTree.word, coarseShiftCost, hword, List.length_ofFn,
      zero_add] at hbound ⊢
    nlinarith

/-- Section 3's second deterministic distortion inequality for the
executable finite coarse tree, conditional only on the guessed distance. -/
theorem coarseTreeValue_edit_upper {B D : ℕ} {α : Type u} [DecidableEq α]
    (tree : CoarseSourceTree B α D) (target : List α) (k : ℕ)
    (hguess : edit tree.word target ≤ k) :
    coarseTreeValue tree target k ≤ (1 + 2 * B * D) * edit tree.word target := by
  exact coarseShiftCost_edit_upper k target tree [] target [] 0 (coarseRootShift k)
    (by simp) (by simp [coarseRootShift]) (by simpa using hguess)

end EditApproximation

end OAI
