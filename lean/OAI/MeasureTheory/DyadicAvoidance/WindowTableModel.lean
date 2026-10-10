import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel
import OAI.MeasureTheory.DyadicAvoidance.WindowData

namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

variable {M d g r₀ : ℕ}

/-- The nondefault child edge used by a selector table. -/
def selectorEdge (P : Node M d) (i : Fin M) : List (Child M) :=
  P.val ++ [i.castSucc]

lemma selectorEdge_valid (P : Node M d) (i : Fin M) :
    ValidWindowEdge d (selectorEdge P i) := by
  constructor
  · simp [selectorEdge]
  · have hP := P.property
    simp only [selectorEdge, List.length_append, List.length_singleton]
    omega

lemma leaf_valid (hd : 0 < d) (L : Leaf M d) : ValidWindowEdge d L.val := by
  constructor
  · intro h
    have hL := L.property
    rw [h] at hL
    simp only [List.length_nil] at hL
    omega
  · exact le_of_eq L.property

/-- Canonical selector resolutions are the incoming window endpoints. -/
def selectorEndpoints (W : WindowData (M + 1) d g r₀) : Node M d → Fin M → ℕ :=
  fun P i => W.b (selectorEdge P i)

/-- Each terminal table uses its leaf's incoming-edge endpoint. -/
def terminalEndpoints (W : WindowData (M + 1) d g r₀) : Leaf M d → ℕ :=
  fun L => W.b L.val

lemma selectorEndpoints_descendant_le
    (W : WindowData (M + 1) d g r₀) (A : List (Child M))
    (hA : ValidWindowEdge d A) (P : Node M d) (i : Fin M)
    (hprefix : A.IsPrefix P.val) : selectorEndpoints W P i ≤ W.bstar A := by
  exact (W.descendant_bounds A (selectorEdge P i) hA (selectorEdge_valid P i)
    (hprefix.trans (List.prefix_append _ _))).2

lemma terminalEndpoints_descendant_le
    (W : WindowData (M + 1) d g r₀) (hd : 0 < d) (A : List (Child M))
    (hA : ValidWindowEdge d A) (L : Leaf M d)
    (hprefix : A.IsPrefix L.val) : terminalEndpoints W L ≤ W.bstar A := by
  exact (W.descendant_bounds A L.val hA (leaf_valid hd L) hprefix).2

lemma incoming_le_terminalEndpoints
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) (L : Leaf M d)
    (hprefix : (selectorEdge P i).IsPrefix L.val) :
    selectorEndpoints W P i ≤ terminalEndpoints W L := by
  have hd : 0 < d := by have := P.property; omega
  exact (W.descendant_bounds (selectorEdge P i) L.val
    (selectorEdge_valid P i) (leaf_valid hd L) hprefix).1

lemma selectorEndpoints_self_le
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) :
    selectorEndpoints W P i ≤ W.bstar (selectorEdge P i) := by
  exact (W.descendant_bounds _ _ (selectorEdge_valid P i) (selectorEdge_valid P i)
    (by exact ⟨[], by simp⟩)).2

lemma child_window_length
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) :
    W.length (selectorEdge P i) = W.r (d - P.val.length) := by
  simp [WindowData.length, selectorEdge]

lemma selector_window_endpoint
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) :
    selectorEndpoints W P i + 1 = W.a (selectorEdge P i) + W.r (d - P.val.length) := by
  have h := W.endpoint (selectorEdge P i) (selectorEdge_valid P i)
  simpa [selectorEndpoints, selectorEdge] using h

end Problem310.FiniteTableModel

end

end OAI
