import Mathlib.Combinatorics.SimpleGraph.Paths
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanRoute

namespace OAI

/-! A finite unit-step route has a simple subroute with no larger length. -/

namespace ContinuumCoulomb

def qmaSquareGrid : SimpleGraph (ℕ × ℕ) where
  Adj p q := Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1
  symm := ⟨by intro p q h; simpa only [Nat.dist_comm] using h⟩
  loopless := ⟨by intro p; simp⟩

theorem qmaManhattanPoint_adj (p q : ℕ × ℕ) (k : ℕ)
    (hk : k < qmaManhattanLength p q) :
    qmaSquareGrid.Adj (qmaManhattanPoint p q k) (qmaManhattanPoint p q (k+1)) :=
  qmaManhattanPoint_step p q k hk

def qmaGridWalk (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    qmaSquareGrid.Walk (p 0) (p L) :=
  match L with
  | 0 => .nil
  | L+1 => .cons (hstep 0 (by omega))
      (qmaGridWalk (fun k => p (k+1)) L (fun k hk => hstep (k+1) (by omega)))

theorem qmaGridWalk_length (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    (qmaGridWalk p L hstep).length = L := by
  induction L generalizing p with
  | zero => rfl
  | succ L ih => simp only [qmaGridWalk,SimpleGraph.Walk.length_cons,ih]

theorem qmaGridWalk_support (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) {z : ℕ × ℕ}
    (hz : z ∈ (qmaGridWalk p L hstep).support) : ∃ k ≤ L, p k = z := by
  induction L generalizing p with
  | zero =>
    simp only [qmaGridWalk,SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
    exact ⟨0,le_rfl,hz.symm⟩
  | succ L ih =>
    simp only [qmaGridWalk,SimpleGraph.Walk.support_cons,List.mem_cons] at hz
    rcases hz with hz | hz
    · exact ⟨0,by omega,hz.symm⟩
    · obtain ⟨k,hk,he⟩ := ih (fun k => p (k+1)) _ hz
      exact ⟨k+1,by omega,he⟩

noncomputable def qmaSimpleGridPath (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    qmaSquareGrid.Path (p 0) (p L) := (qmaGridWalk p L hstep).toPath

theorem qmaSimpleGridPath_length (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    (qmaSimpleGridPath p L hstep).val.length ≤ L :=
  ((qmaGridWalk p L hstep).length_bypass_le_length).trans_eq (qmaGridWalk_length p L hstep)

theorem qmaSimpleGridPath_support (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) {z : ℕ × ℕ}
    (hz : z ∈ (qmaSimpleGridPath p L hstep).val.support) : ∃ k ≤ L, p k = z :=
  qmaGridWalk_support p L hstep ((qmaGridWalk p L hstep).support_toPath_subset_support hz)


theorem qmaGridPath_getVert_step {u v : ℕ × ℕ} (P : qmaSquareGrid.Path u v)
    (i : Fin P.val.length) :
    qmaSquareGrid.Adj (P.val.getVert i.castSucc.val) (P.val.getVert i.succ.val) :=
  P.val.adj_getVert_succ i.isLt

end ContinuumCoulomb

end OAI
