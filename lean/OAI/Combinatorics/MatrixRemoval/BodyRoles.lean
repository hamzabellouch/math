import OAI.Combinatorics.MatrixRemoval.Model

namespace OAI

/-!
# Exact body signatures and extraction of body roles

All signatures refer to `fixedH`, including its zero entries.
-/

namespace Problem348.BodySignatures52

def anchorIndex (u : Fin 64) : Fin 66 := ⟨u.val, by omega⟩

def bodyIndex (b : Fin 2) : Fin 66 := ⟨64 + b.val, by omega⟩

theorem fixedH_anchor_anchor (u v : Fin 64) :
    fixedH (anchorIndex u) (anchorIndex v) = anchor64 u v := by
  simp [fixedH, anchorIndex, u.isLt, v.isLt]

theorem fixedH_body_anchor (b : Fin 2) (v : Fin 64) :
    fixedH (bodyIndex b) (anchorIndex v) = decide (v.val = b.val) := by
  fin_cases b <;> simp [fixedH, bodyIndex, anchorIndex, v.isLt]

theorem fixedH_anchor_body (u : Fin 64) (b : Fin 2) :
    fixedH (anchorIndex u) (bodyIndex b) = decide (u.val = b.val) := by
  fin_cases b <;> simp [fixedH, bodyIndex, anchorIndex, u.isLt]

theorem fixedH_body_body (b c : Fin 2) :
    fixedH (bodyIndex b) (bodyIndex c) = decide (b.val = 1 ∨ c.val = 0) := by
  fin_cases b <;> fin_cases c <;> rfl

/-- No anchor row has either of the two body-row signatures. -/
theorem anchor64_row_ne_body_signature (u : Fin 64) (b : Fin 2) :
    (fun v => anchor64 u v) ≠ (fun v : Fin 64 => decide (v.val = b.val)) := by
  intro h
  have h2 := congrFun h (2 : Fin 64)
  have h3 := congrFun h (3 : Fin 64)
  fin_cases b <;> simp [anchor64] at h2 h3 <;> omega

/-- No anchor column has either of the two body-column signatures. -/
theorem anchor64_col_ne_body_signature (v : Fin 64) (b : Fin 2) :
    (fun u => anchor64 u v) ≠ (fun u : Fin 64 => decide (u.val = b.val)) := by
  intro h
  have h2 := congrFun h (2 : Fin 64)
  have h3 := congrFun h (3 : Fin 64)
  fin_cases b <;> simp [anchor64] at h2 h3 <;> omega

theorem zero_ne_body_signature (b : Fin 2) :
    (fun _ : Fin 64 => false) ≠ (fun v : Fin 64 => decide (v.val = b.val)) := by
  intro h
  have hb := congrFun h (⟨b.val, by omega⟩ : Fin 64)
  simp at hb

theorem copy_body_row_signature {n : ℕ} {A : BinaryMatrix n}
    {rc : IncreasingMap 66 n × IncreasingMap 66 n}
    (hcopy : rc ∈ orderedCopies fixedH A) (b : Fin 2) (v : Fin 64) :
    A (rc.1.val (bodyIndex b)) (rc.2.val (anchorIndex v)) =
      decide (v.val = b.val) := by
  classical
  have hm := (Finset.mem_filter.mp hcopy).2 (bodyIndex b) (anchorIndex v)
  exact hm.trans (fixedH_body_anchor b v)

theorem copy_body_col_signature {n : ℕ} {A : BinaryMatrix n}
    {rc : IncreasingMap 66 n × IncreasingMap 66 n}
    (hcopy : rc ∈ orderedCopies fixedH A) (b : Fin 2) (u : Fin 64) :
    A (rc.1.val (anchorIndex u)) (rc.2.val (bodyIndex b)) =
      decide (u.val = b.val) := by
  classical
  have hm := (Finset.mem_filter.mp hcopy).2 (anchorIndex u) (bodyIndex b)
  exact hm.trans (fixedH_anchor_body u b)

end Problem348.BodySignatures52

end OAI
