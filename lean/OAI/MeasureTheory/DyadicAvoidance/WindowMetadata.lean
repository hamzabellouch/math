import OAI.MeasureTheory.DyadicAvoidance.TreePreorder
import OAI.MeasureTheory.DyadicAvoidance.WindowRecursion
import OAI.MeasureTheory.DyadicAvoidance.WindowPlacement

namespace OAI

noncomputable section

namespace Problem310.WindowMetadata

open TreePreorder

/-- The canonical preorder index of an edge. -/
def edgeIndex {q d : ℕ} (e : Edge q d) : ℕ := (edgePaths q d).idxOf e.val

/-- Numeric incoming-window height for an edge path. -/
def edgeHeight {q d : ℕ} (e : Edge q d) : ℕ := d + 1 - e.val.length

/-- Window lengths in precisely the canonical tree-edge preorder. -/
def lengths (q d g r₀ : ℕ) : List ℕ :=
  (edgePaths q d).map (fun P => WindowRecursion.length q g r₀ (d + 1 - P.length))

/-- The length function consumed by the canonical numeric placement API. -/
def lengthAt (q d g r₀ : ℕ) : ℕ → ℕ :=
  WindowPlacement.lengthAt (lengths q d g r₀)

def start {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : ℕ :=
  WindowPlacement.start (lengthAt q d g r₀) g (edgeIndex e)

def finish {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : ℕ :=
  WindowPlacement.finish (lengthAt q d g r₀) g (edgeIndex e)

def window {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : Finset ℕ :=
  WindowPlacement.window (lengthAt q d g r₀) g (edgeIndex e)

theorem edgeIndex_lt {q d : ℕ} (e : Edge q d) : edgeIndex e < edgeCount q d := by
  simpa only [edgeIndex, length_edgePaths] using (List.idxOf_lt_length_iff.mpr e.property)

theorem edgeHeight_pos {q d : ℕ} (e : Edge q d) : 0 < edgeHeight e := by
  have := edge_length_le e
  unfold edgeHeight
  omega

@[simp] theorem lengthAt_edgeIndex {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) :
    lengthAt q d g r₀ (edgeIndex e) = WindowRecursion.length q g r₀ (edgeHeight e) := by
  simp only [lengthAt, lengths, WindowPlacement.lengthAt, edgeIndex,
    List.getElem?_map, List.getElem?_idxOf e.property, Option.map_some, Option.getD_some,
    edgeHeight]

theorem lengthAt_edgeIndex_pos {q d : ℕ} (g : ℕ) {r₀ : ℕ}
    (hr₀ : 0 < r₀) (e : Edge q d) : 0 < lengthAt q d g r₀ (edgeIndex e) := by
  rw [lengthAt_edgeIndex]
  exact WindowRecursion.length_pos q g r₀ _ hr₀

theorem threshold_le_window_length {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) :
    r₀ ≤ lengthAt q d g r₀ (edgeIndex e) := by
  rw [lengthAt_edgeIndex]
  exact WindowRecursion.threshold_le_length q g r₀ _

@[simp] theorem card_window {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) :
    (window g r₀ e).card = WindowRecursion.length q g r₀ (edgeHeight e) := by
  simp only [window, WindowPlacement.card_window, lengthAt_edgeIndex]

theorem three_le_start {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : 3 ≤ start g r₀ e :=
  WindowPlacement.three_le_start _ _ _

theorem start_le_finish {q d : ℕ} (g : ℕ) {r₀ : ℕ}
    (hr₀ : 0 < r₀) (e : Edge q d) : start g r₀ e ≤ finish g r₀ e :=
  WindowPlacement.start_le_finish (lengthAt_edgeIndex_pos g hr₀ e)

@[simp] theorem mem_window {q d : ℕ} {g r₀ n : ℕ} {e : Edge q d} :
    n ∈ window g r₀ e ↔ start g r₀ e ≤ n ∧ n ≤ finish g r₀ e :=
  WindowPlacement.mem_window

theorem three_le_of_mem {q d : ℕ} {g r₀ n : ℕ} {e : Edge q d}
    (hn : n ∈ window g r₀ e) : 3 ≤ n :=
  WindowPlacement.three_le_of_mem hn

theorem gap_of_index_lt {q d : ℕ} (g r₀ : ℕ) {e f : Edge q d}
    (h : edgeIndex e < edgeIndex f) : finish g r₀ e + g < start g r₀ f :=
  WindowPlacement.gap_of_lt _ _ h

@[simp] theorem child_height {q d : ℕ} (P : List (Fin q)) (hP : P.length < d)
    (i : Fin q) : edgeHeight (childEdge P hP i) = d - P.length := by
  simp [edgeHeight, childEdge, mkEdge]

@[simp] theorem child_window_card {q d : ℕ} (g r₀ : ℕ)
    (P : List (Fin q)) (hP : P.length < d) (i : Fin q) :
    (window g r₀ (childEdge P hP i)).card =
      WindowRecursion.length q g r₀ (d - P.length) := by
  rw [card_window, child_height]

end Problem310.WindowMetadata

end

end OAI
