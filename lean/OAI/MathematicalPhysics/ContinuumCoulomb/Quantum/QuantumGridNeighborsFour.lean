import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridWalk

namespace OAI

/-! The four local ports of an interior square-grid point. -/

namespace ContinuumCoulomb

def qmaGridNeighbor (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  ![(p.1+1,p.2),(p.1,p.2+1),(p.1-1,p.2),(p.1,p.2-1)] a

theorem qmaGridNeighbor_injective (p : ℕ × ℕ) (hx : 0 < p.1) (hy : 0 < p.2) :
    Function.Injective (qmaGridNeighbor p) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [qmaGridNeighbor] at h ⊢ <;> omega

theorem qmaGridNeighbor_adj (p : ℕ × ℕ) (hx : 0 < p.1) (hy : 0 < p.2) (a : Fin 4) :
    qmaSquareGrid.Adj p (qmaGridNeighbor p a) := by
  fin_cases a <;> simp [qmaGridNeighbor,qmaSquareGrid,Nat.dist] <;> omega

theorem qmaGridNeighbor_exists {p q : ℕ × ℕ} (ha : qmaSquareGrid.Adj p q) :
    ∃ a : Fin 4, qmaGridNeighbor p a = q := by
  change Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 at ha
  have h : (q.1 = p.1+1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 = p.2+1) ∨
      (q.1+1 = p.1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2+1 = p.2) := by
    unfold Nat.dist at ha
    omega
  rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ⟨0,Prod.ext hx.symm hy.symm⟩
  · exact ⟨1,Prod.ext hx.symm hy.symm⟩
  · refine ⟨2,?_⟩
    apply Prod.ext <;> simp [qmaGridNeighbor] <;> omega
  · refine ⟨3,?_⟩
    apply Prod.ext <;> simp [qmaGridNeighbor] <;> omega

def qmaGridNeighborIndex (p q : ℕ × ℕ) : Fin 4 :=
  if q.1 = p.1+1 then 0 else if q.2 = p.2+1 then 1 else if q.1+1 = p.1 then 2 else 3

theorem qmaGridNeighborIndex_spec {p q : ℕ × ℕ} (hx : 0 < p.1) (hy : 0 < p.2)
    (ha : qmaSquareGrid.Adj p q) : qmaGridNeighbor p (qmaGridNeighborIndex p q) = q := by
  obtain ⟨a,rfl⟩ := qmaGridNeighbor_exists ha
  rcases p with ⟨x,y⟩
  have hs : x-1+1 = x := by omega
  fin_cases a <;> simp [qmaGridNeighborIndex,qmaGridNeighbor,hs]

end ContinuumCoulomb

end OAI
