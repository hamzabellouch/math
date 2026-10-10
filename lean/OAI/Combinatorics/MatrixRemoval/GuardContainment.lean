import OAI.Combinatorics.MatrixRemoval.HostSampling
import OAI.Combinatorics.MatrixRemoval.GuardedPath

namespace OAI

/-!
Containment of guarded-path cells in the protected sampling set.
The geometric validity of a selection and the cellwise counting bound
are separate requirements.
-/

namespace Problem348.Construction.HostSampling

open Problem348.TreeSampling Problem348.GuardedPath

variable {h n : ℕ}

/-- A selected row after the independent row reindexing. -/
def RowChosen (row : Position h ≃ Fin n) (s : Seeds (2 ^ h)) (r : Fin n) : Prop :=
  coordinate s.1 s.2.1 (row.symm r) = offset (row.symm r)

/-- A selected column after the independent column reindexing. -/
def ColChosen (col : Position h ≃ Fin n) (s : Seeds (2 ^ h)) (c : Fin n) : Prop :=
  coordinate s.1 s.2.2 (col.symm c) = offset (col.symm c)

/-- The exact cell predicate needed by `transported_guard_frequency`. -/
def GoodCell (row col : Position h ≃ Fin n) (s : Seeds (2 ^ h))
    (rc : Fin n × Fin n) : Prop :=
  Protected (row.symm rc.1) (col.symm rc.2) ∧
    Selected s (row.symm rc.1) (col.symm rc.2)

 theorem goodCell_of_chosen {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {r c : Fin n} (hp : Protected (row.symm r) (col.symm c))
    (hr : RowChosen row s r) (hc : ColChosen col s c) :
    GoodCell row col s (r, c) :=
  ⟨hp, Prod.ext hr hc⟩

/-- A selected anchor frame, considered only as a family of protected positions. -/
structure FrameChosen (row col : Position h ≃ Fin n) (s : Seeds (2 ^ h))
    (F : AnchorFrame n) : Prop where
  row_independent : ∀ u, sampleDepth (row.symm (F.rows.val u)) = none
  col_independent : ∀ v, sampleDepth (col.symm (F.cols.val v)) = none
  row_chosen : ∀ u, RowChosen row s (F.rows.val u)
  col_chosen : ∀ v, ColChosen col s (F.cols.val v)

/-- All anchor and signature cells of a chosen frame are protected and selected. -/
theorem FrameChosen.cell_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {F : AnchorFrame n} (hF : FrameChosen row col s F)
    {r₀ r₁ c₀ c₁ : Fin n}
    (hr₀ : RowChosen row s r₀) (hr₁ : RowChosen row s r₁)
    (hc₀ : ColChosen col s c₀) (hc₁ : ColChosen col s c₁)
    {rc : Fin n × Fin n} (hcell : F.Cell r₀ r₁ c₀ c₁ rc) :
    GoodCell row col s rc := by
  rcases hcell with ⟨u, v, rfl⟩ | ⟨v, rfl | rfl⟩ | ⟨u, rfl | rfl⟩
  · exact goodCell_of_chosen (Or.inl (hF.row_independent u))
      (hF.row_chosen u) (hF.col_chosen v)
  · exact goodCell_of_chosen (Or.inr (Or.inl (hF.col_independent v)))
      hr₀ (hF.col_chosen v)
  · exact goodCell_of_chosen (Or.inr (Or.inl (hF.col_independent v)))
      hr₁ (hF.col_chosen v)
  · exact goodCell_of_chosen (Or.inl (hF.row_independent u))
      (hF.row_chosen u) hc₀
  · exact goodCell_of_chosen (Or.inl (hF.row_independent u))
      (hF.row_chosen u) hc₁

/-- Purely geometric sampling facts, separate from the host's matrix values. -/
structure PathChosen (row col : Position h ≃ Fin n) (s : Seeds (2 ^ h))
    (P : Selection n) : Prop where
  xp_chosen : ∀ i, i ≤ h → RowChosen row s (P.xp i)
  xm_chosen : ∀ i, i ≤ h → RowChosen row s (P.xm i)
  yp_chosen : ∀ i, i ≤ h → ColChosen col s (P.yp i)
  ym_chosen : ∀ i, i ≤ h → ColChosen col s (P.ym i)
  xd_chosen : RowChosen row s P.xd
  yd_chosen : ColChosen col s P.yd
  xd_independent : sampleDepth (row.symm P.xd) = none
  yd_independent : sampleDepth (col.symm P.yd) = none
  root_plus : Protected (row.symm (P.xp 0)) (col.symm (P.yp 0))
  root_minus : Protected (row.symm (P.xm 0)) (col.symm (P.ym 0))
  vertical_plus : ∀ i, i < h → FrameChosen row col s (P.vPlus i)
  vertical_minus : ∀ i, i < h → FrameChosen row col s (P.vMinus i)
  horizontal_plus : ∀ i, i < h → FrameChosen row col s (P.wPlus i)
  horizontal_minus : ∀ i, i < h → FrameChosen row col s (P.wMinus i)

 theorem PathChosen.core_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {P : Selection n} (hP : PathChosen row col s P)
    {rc : Fin n × Fin n} (hc : P.CoreCell h rc) : GoodCell row col s rc := by
  rcases hc with rfl | rfl | ⟨i, hi, rfl | rfl | rfl | rfl⟩
  · exact goodCell_of_chosen hP.root_plus
      (hP.xp_chosen 0 (Nat.zero_le _)) (hP.yp_chosen 0 (Nat.zero_le _))
  · exact goodCell_of_chosen hP.root_minus
      (hP.xm_chosen 0 (Nat.zero_le _)) (hP.ym_chosen 0 (Nat.zero_le _))
  · exact goodCell_of_chosen (Or.inr (Or.inl hP.yd_independent))
      (hP.xp_chosen i hi) hP.yd_chosen
  · exact goodCell_of_chosen (Or.inr (Or.inl hP.yd_independent))
      (hP.xm_chosen i hi) hP.yd_chosen
  · exact goodCell_of_chosen (Or.inl hP.xd_independent)
      hP.xd_chosen (hP.yp_chosen i hi)
  · exact goodCell_of_chosen (Or.inl hP.xd_independent)
      hP.xd_chosen (hP.ym_chosen i hi)

 theorem PathChosen.edge_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {P : Selection n} (hP : PathChosen row col s P) {i : ℕ} (hi : i < h)
    {rc : Fin n × Fin n} (hc : P.EdgeCell i rc) : GoodCell row col s rc := by
  have hil : i ≤ h := Nat.le_of_lt hi
  have his : i + 1 ≤ h := hi
  rcases hc with hc | hc | hc | hc
  · exact (hP.vertical_plus i hi).cell_good
      (hP.xp_chosen (i + 1) his) (hP.xp_chosen i hil)
      hP.yd_chosen (hP.yp_chosen i hil) hc
  · exact (hP.vertical_minus i hi).cell_good
      (hP.xm_chosen i hil) (hP.xm_chosen (i + 1) his)
      hP.yd_chosen (hP.ym_chosen i hil) hc
  · exact (hP.horizontal_plus i hi).cell_good
      (hP.xp_chosen (i + 1) his) hP.xd_chosen
      (hP.yp_chosen i hil) (hP.yp_chosen (i + 1) his) hc
  · exact (hP.horizontal_minus i hi).cell_good
      (hP.xm_chosen (i + 1) his) hP.xd_chosen
      (hP.ym_chosen (i + 1) his) (hP.ym_chosen i hil) hc

/-- Every actual guarded-path cell is in the protected selected-cell event. -/
theorem PathChosen.guard_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {P : Selection n} (hP : PathChosen row col s P)
    {rc : Fin n × Fin n} (hc : rc ∈ P.guards h) : GoodCell row col s rc := by
  rw [Selection.mem_guards] at hc
  rcases hc with hc | ⟨i, hi, hc⟩
  · exact hP.core_good hc
  · exact hP.edge_good hi hc

/-- The frequency bound for any concretely chosen family of paths. -/
theorem path_guard_frequency (row col : Position h ≃ Fin n)
    (P : Seeds (2 ^ h) → Selection n)
    (hP : ∀ s, PathChosen row col s (P s)) (rc : Fin n × Fin n) :
    (Finset.univ.filter fun s => rc ∈ (P s).guards h).card * (2 ^ h) ^ 2 ≤
      Fintype.card (Seeds (2 ^ h)) := by
  classical
  exact transported_guard_frequency row col (fun s => (P s).guards h)
    (fun s _ hc => (hP s).guard_good hc) rc

end Problem348.Construction.HostSampling

end OAI
