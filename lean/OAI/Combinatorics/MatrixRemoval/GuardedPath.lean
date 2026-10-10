import OAI.Combinatorics.MatrixRemoval.GuardedFrame

namespace OAI

/-!
A deterministic arbitrary-repair obstruction for the fixed binary pattern.
A selection records one common tree path, dummy positions, and four selected
anchor frames per edge. Its guards contain only root, dummy, anchor, and
anchor/body signature cells -- never the unconstrained variable body cells.
-/

noncomputable section
namespace Problem348.GuardedPath

/-- Selected positions; no host construction or matching assumptions are hidden
in this data structure. Values past the chosen depth are irrelevant. -/
structure Selection (n : ℕ) where
  xp : ℕ → Fin n
  xm : ℕ → Fin n
  yp : ℕ → Fin n
  ym : ℕ → Fin n
  xd : Fin n
  yd : Fin n
  vPlus : ℕ → AnchorFrame n
  vMinus : ℕ → AnchorFrame n
  wPlus : ℕ → AnchorFrame n
  wMinus : ℕ → AnchorFrame n

namespace Selection
variable {n : ℕ}

/-- Root and dummy cells needed for Boolean propagation. -/
def CoreCell (P : Selection n) (h : ℕ) (rc : Fin n × Fin n) : Prop :=
  rc = (P.xp 0, P.yp 0) ∨ rc = (P.xm 0, P.ym 0) ∨
  ∃ i, i ≤ h ∧ (rc = (P.xp i, P.yd) ∨ rc = (P.xm i, P.yd) ∨
    rc = (P.xd, P.yp i) ∨ rc = (P.xd, P.ym i))

/-- Anchor and signature cells for the four modes at one edge. -/
def EdgeCell (P : Selection n) (i : ℕ) (rc : Fin n × Fin n) : Prop :=
  (P.vPlus i).Cell (P.xp (i + 1)) (P.xp i) P.yd (P.yp i) rc ∨
  (P.vMinus i).Cell (P.xm i) (P.xm (i + 1)) P.yd (P.ym i) rc ∨
  (P.wPlus i).Cell (P.xp (i + 1)) P.xd (P.yp i) (P.yp (i + 1)) rc ∨
  (P.wMinus i).Cell (P.xm (i + 1)) P.xd (P.ym (i + 1)) (P.ym i) rc

/-- The protected cells of the whole selected path. -/
def GuardCell (P : Selection n) (h : ℕ) (rc : Fin n × Fin n) : Prop :=
  P.CoreCell h rc ∨ ∃ i, i < h ∧ P.EdgeCell i rc

def guards (P : Selection n) (h : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (P.GuardCell h)

@[simp] theorem mem_guards (P : Selection n) (h : ℕ) (rc : Fin n × Fin n) :
    rc ∈ P.guards h ↔ P.GuardCell h rc := by
  classical
  simp [guards]

/-- Explicit original-matrix conditions on a selected path. The frame validity
contains all required order comparisons and all 64-anchor signatures. -/
structure Valid (P : Selection n) (A : BinaryMatrix n) (h : ℕ) : Prop where
  root_plus : A (P.xp 0) (P.yp 0) = true
  root_minus : A (P.xm 0) (P.ym 0) = false
  dummy_col : ∀ i, i ≤ h → A (P.xp i) P.yd = true ∧ A (P.xm i) P.yd = true
  dummy_row : ∀ i, i ≤ h → A P.xd (P.yp i) = true ∧ A P.xd (P.ym i) = true
  leaf_row : P.xp h = P.xm h
  leaf_col : P.yp h = P.ym h
  vertical_plus : ∀ i, i < h →
    (P.vPlus i).Valid A (P.xp (i + 1)) (P.xp i) P.yd (P.yp i)
  vertical_minus : ∀ i, i < h →
    (P.vMinus i).Valid A (P.xm i) (P.xm (i + 1)) P.yd (P.ym i)
  horizontal_plus : ∀ i, i < h →
    (P.wPlus i).Valid A (P.xp (i + 1)) P.xd (P.yp i) (P.yp (i + 1))
  horizontal_minus : ∀ i, i < h →
    (P.wMinus i).Valid A (P.xm (i + 1)) P.xd (P.ym (i + 1)) (P.ym i)

/-- If no guard cell was edited, every condition needed for path propagation
and exact anchor completion survives. -/
theorem Valid.transfer {P : Selection n} {A B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid A h)
    (hag : ∀ rc ∈ P.guards h, A rc.1 rc.2 = B rc.1 rc.2) :
    P.Valid B h := by
  have hc : ∀ rc, P.CoreCell h rc → A rc.1 rc.2 = B rc.1 rc.2 := by
    intro rc hrc
    exact hag rc ((mem_guards P h rc).mpr (Or.inl hrc))
  have he : ∀ i, i < h → ∀ rc, P.EdgeCell i rc → A rc.1 rc.2 = B rc.1 rc.2 := by
    intro i hi rc hrc
    exact hag rc ((mem_guards P h rc).mpr (Or.inr ⟨i, hi, hrc⟩))
  refine ⟨?_, ?_, ?_, ?_, hv.leaf_row, hv.leaf_col, ?_, ?_, ?_, ?_⟩
  · exact (hc _ (Or.inl rfl)).symm.trans hv.root_plus
  · exact (hc _ (Or.inr (Or.inl rfl))).symm.trans hv.root_minus
  · intro i hi
    constructor
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inl rfl⟩))).symm.trans
        (hv.dummy_col i hi).1
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inl rfl)⟩))).symm.trans
        (hv.dummy_col i hi).2
  · intro i hi
    constructor
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩))).symm.trans
        (hv.dummy_row i hi).1
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩))).symm.trans
        (hv.dummy_row i hi).2
  · intro i hi
    exact (hv.vertical_plus i hi).transfer (fun rc hrc => he i hi rc (Or.inl hrc))
  · intro i hi
    exact (hv.vertical_minus i hi).transfer
      (fun rc hrc => he i hi rc (Or.inr (Or.inl hrc)))
  · intro i hi
    exact (hv.horizontal_plus i hi).transfer
      (fun rc hrc => he i hi rc (Or.inr (Or.inr (Or.inl hrc))))
  · intro i hi
    exact (hv.horizontal_minus i hi).transfer
      (fun rc hrc => he i hi rc (Or.inr (Or.inr (Or.inr hrc))))

/-- Every valid selected path gives a copy of the exact fixed H. -/
theorem Valid.not_HFree {P : Selection n} {B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid B h) : ¬ HFree fixedH B := by
  obtain ⟨i, hi, hb⟩ := PathPropagation.exists_modeBody hv.root_plus hv.root_minus
    hv.dummy_col hv.dummy_row hv.leaf_row hv.leaf_col
  rcases hb with hb | hb | hb | hb
  · exact (hv.vertical_plus i hi).not_HFree hb
  · exact (hv.vertical_minus i hi).not_HFree hb
  · exact (hv.horizontal_plus i hi).not_HFree hb
  · exact (hv.horizontal_minus i hi).not_HFree hb

/-- Arbitrary edits outside the finite guard set cannot destroy all copies. -/
theorem not_HFree_of_agree {P : Selection n} {A B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid A h)
    (hag : ∀ rc ∈ P.guards h, A rc.1 rc.2 = B rc.1 rc.2) :
    ¬ HFree fixedH B :=
  (hv.transfer hag).not_HFree

/-- Every H-free repair must hit the guard set of each valid selected path.
This is a statement about all repairs, not just destroying original copies. -/
theorem repair_hits_guards {P : Selection n} {A B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid A h) (hfree : HFree fixedH B) :
    ∃ rc ∈ P.guards h, A rc.1 rc.2 ≠ B rc.1 rc.2 := by
  classical
  by_contra hn
  push Not at hn
  exact not_HFree_of_agree hv hn hfree

end Selection
end Problem348.GuardedPath

end

end OAI
