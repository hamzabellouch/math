import OAI.MeasureTheory.DyadicAvoidance.TreePreorder
import OAI.MeasureTheory.DyadicAvoidance.WindowSpanSum

namespace OAI

universe u_α

namespace Problem310.TreeSpanBridge

open TreePreorder

/-- Incoming-window lengths listed in the tree's edge preorder. -/
def weights (q d : ℕ) (r : ℕ → ℕ) : List ℕ :=
  (edgePaths q d).map fun p => r (d + 1 - p.length)

@[simp] theorem weights_zero (q : ℕ) (r : ℕ → ℕ) : weights q 0 r = [] := rfl

/-- Each child contributes its incoming length followed by the weights of a
complete subtree of one smaller height. This is independent of the child label. -/
theorem weights_succ (q d : ℕ) (r : ℕ → ℕ) :
    weights q (d + 1) r =
      (List.finRange q).flatMap (fun _ => r (d + 1) :: weights q d r) := by
  simp only [weights, edgePaths, List.map_flatMap, List.map_cons,
    List.length_cons, List.map_map, Function.comp_def]
  congr 2
  funext i
  congr 1
  apply List.map_congr_left
  intro p hp
  congr 1
  omega


/-- An edge and all descendants under it, in their contiguous preorder block. -/
def subtreeBlock (q d : ℕ) (p : List (Fin q)) : List (List (Fin q)) :=
  p :: (edgePaths q (d - p.length)).map (fun v => p ++ v)

theorem childBlock_infix (q d : ℕ) (i : Fin q) :
    ([i] :: (edgePaths q d).map (List.cons i)) <:+: edgePaths q (d + 1) := by
  have hi : [i] <:+: List.finRange q := (List.singleton_infix_iff i (List.finRange q)).mpr (by simp)
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, edgePaths] using
    hi.flatMap (fun j => [j] :: (edgePaths q d).map (List.cons j))

/-- Every rooted descendant block is contiguous in the global edge preorder. -/
theorem subtreeBlock_infix (q d : ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    subtreeBlock q d p <:+: edgePaths q d := by
  induction p generalizing d with
  | nil => exact (hp rfl).elim
  | cons i p ih =>
    cases d with
    | zero => simp at hlen
    | succ d =>
      cases p with
      | nil =>
        simpa [subtreeBlock] using childBlock_infix q d i
      | cons j p =>
        have hlen' : (j :: p).length ≤ d := by simpa using hlen
        have hsub := (ih d (by simp) hlen').map (List.cons i)
        have htail : (edgePaths q d).map (List.cons i) <:+:
            [i] :: (edgePaths q d).map (List.cons i) :=
          ⟨[[i]], [], by simp⟩
        have hfull := hsub.trans (htail.trans (childBlock_infix q d i))
        simpa [subtreeBlock, List.map_map, Function.comp_def] using hfull

/-- Global-depth weights on one descendant block are exactly the incoming
length followed by the weights of the complete residual-height subtree. -/
theorem map_weights_subtreeBlock (q d : ℕ) (r : ℕ → ℕ) (p : List (Fin q))
    (hlen : p.length ≤ d) :
    (subtreeBlock q d p).map (fun v => r (d + 1 - v.length)) =
      r (d + 1 - p.length) :: weights q (d - p.length) r := by
  simp only [subtreeBlock, List.map_cons, List.map_map, Function.comp_def,
    List.length_append, weights]
  congr 1
  apply List.map_congr_left
  intro v hv
  congr 1
  omega

/-- The incoming edge and descendant weights form a contiguous block of the
full weighted preorder, ready for the numerical child-span estimate. -/
theorem weights_subtree_infix (q d : ℕ) (r : ℕ → ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    (r (d + 1 - p.length) :: weights q (d - p.length) r) <:+: weights q d r := by
  have h := (subtreeBlock_infix q d p hp hlen).map (fun v => r (d + 1 - v.length))
  rwa [map_weights_subtreeBlock q d r p hlen] at h

/-- A nonempty contiguous block in a duplicate-free list starts at the index
of its first entry. -/
theorem take_drop_idxOf_of_infix {α : Type u_α} [BEq α] [LawfulBEq α]
    (l : List α) (hl : l.Nodup) (a : α) (u : List α) (h : (a :: u) <:+: l) :
    (l.drop (l.idxOf a)).take (u.length + 1) = a :: u := by
  obtain ⟨s, t, rfl⟩ := h
  simp only [List.append_assoc] at hl ⊢
  have hnot : a ∉ s := by
    intro ha
    exact (List.nodup_append.mp hl).2.2 a ha a (by simp) rfl
  rw [List.idxOf_append_of_notMem hnot]
  simp

/-- Exact contiguous slice of the preorder belonging to one rooted child block. -/
theorem subtreeBlock_eq_slice (q d : ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    ((edgePaths q d).drop ((edgePaths q d).idxOf p)).take
      (1 + edgeCount q (d - p.length)) = subtreeBlock q d p := by
  have h := take_drop_idxOf_of_infix (edgePaths q d) (nodup_edgePaths q d) p
    ((edgePaths q (d - p.length)).map (fun v => p ++ v))
    (subtreeBlock_infix q d p hp hlen)
  simpa only [List.length_map, length_edgePaths, Nat.add_comm, subtreeBlock] using h

/-- The weighted preorder slice at an edge is its incoming weight followed by
exactly one residual-height weighted subtree. -/
theorem weights_slice (q d : ℕ) (r : ℕ → ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    ((weights q d r).drop ((edgePaths q d).idxOf p)).take
      (1 + edgeCount q (d - p.length)) =
      r (d + 1 - p.length) :: weights q (d - p.length) r := by
  rw [weights, ← List.map_drop, ← List.map_take, subtreeBlock_eq_slice q d p hp hlen]
  exact map_weights_subtreeBlock q d r p hlen

/-- The path-dependent weight list is exactly the numerical preorder list. -/
theorem weights_eq_preorderLengths (q g r₀ d : ℕ) :
    weights q d (WindowRecursion.length q g r₀) =
      WindowSpanSum.preorderLengths q g r₀ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [weights_succ, WindowSpanSum.preorderLengths, ih]
    simp [List.flatMap]

/-- The exact padded sum of the actual subtree slice in global preorder. -/
theorem paddedSum_weights_slice (q g r₀ d : ℕ) (hq : 1 ≤ q) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    WindowSpanSum.paddedSum g
      (((weights q d (WindowRecursion.length q g r₀)).drop
        ((edgePaths q d).idxOf p)).take (1 + edgeCount q (d - p.length))) =
      WindowRecursion.childSpan q g r₀ (d - p.length) + g := by
  rw [weights_slice q d _ p hp hlen, weights_eq_preorderLengths]
  have heq : d + 1 - p.length = (d - p.length) + 1 := by omega
  rw [heq]
  exact WindowSpanSum.paddedSum_childBlock q g r₀ (d - p.length) hq

/-- The arithmetic padding budget now applies to an actual subtree slice,
not merely to an abstract recursively defined list of lengths. -/
theorem paddedSum_weights_slice_le (q g r₀ d : ℕ) (hq : 1 ≤ q) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    WindowSpanSum.paddedSum g
      (((weights q d (WindowRecursion.length q g r₀)).drop
        ((edgePaths q d).idxOf p)).take (1 + edgeCount q (d - p.length))) ≤
      2 * WindowRecursion.length q g r₀ (d + 1 - p.length) + g := by
  rw [paddedSum_weights_slice q g r₀ d hq p hp hlen]
  have heq : d + 1 - p.length = (d - p.length) + 1 := by omega
  rw [heq]
  exact Nat.add_le_add_right
    (WindowRecursion.childSpan_le_twice_length q g r₀ (d - p.length)) g

/-- Full-list decomposition at the genuine edge index. This is the direct
interface for constructing separated windows from the weighted preorder. -/
theorem weighted_child_decomposition (q g r₀ d : ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    ∃ pre post : List ℕ,
      weights q d (WindowRecursion.length q g r₀) =
        pre ++ (WindowRecursion.length q g r₀ (d + 1 - p.length) ::
          WindowSpanSum.preorderLengths q g r₀ (d - p.length)) ++ post ∧
      pre.length = (edgePaths q d).idxOf p := by
  obtain ⟨s, t, hst⟩ := subtreeBlock_infix q d p hp hlen
  let f : List (Fin q) → ℕ := fun v => WindowRecursion.length q g r₀ (d + 1 - v.length)
  refine ⟨s.map f, t.map f, ?_, ?_⟩
  · change (edgePaths q d).map f = _
    rw [← hst, List.map_append, List.map_append]
    change s.map f ++ (subtreeBlock q d p).map
      (fun v => WindowRecursion.length q g r₀ (d + 1 - v.length)) ++ t.map f = _
    rw [map_weights_subtreeBlock q d _ p hlen, weights_eq_preorderLengths]
  · rw [List.length_map]
    have hnodup : (s ++ (subtreeBlock q d p ++ t)).Nodup := by
      rw [← List.append_assoc, hst]
      exact nodup_edgePaths q d
    have hnot : p ∉ s := by
      intro hps
      exact (List.nodup_append.mp hnodup).2.2 p hps p (by simp [subtreeBlock]) rfl
    rw [← hst, List.append_assoc, List.idxOf_append_of_notMem hnot]
    simp [subtreeBlock]

end Problem310.TreeSpanBridge

end OAI
