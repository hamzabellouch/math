import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChain

namespace OAI

/-! Every port-chain interaction is a vertex ray, a pairing inside one cell,
or the single corridor joining opposite ports of adjacent cells. -/

namespace ContinuumCoulomb

def QMAPortLink (x y : ℕ × ℕ) : Prop :=
  (∃ p a, (x = qmaExpandedPoint p ∧ y = qmaGridPort p a) ∨
    (x = qmaGridPort p a ∧ y = qmaExpandedPoint p)) ∨
  (∃ p a b, x = qmaGridPort p a ∧ y = qmaGridPort p b) ∨
  (∃ p q, qmaSquareGrid.Adj p q ∧ x = qmaDirectedPort p q ∧ y = qmaDirectedPort q p)

theorem QMAPortLink.symm {x y : ℕ × ℕ} (h : QMAPortLink x y) : QMAPortLink y x := by
  rcases h with ⟨p,a,h | h⟩ | ⟨p,a,b,hx,hy⟩ | ⟨p,q,ha,hx,hy⟩
  · exact Or.inl ⟨p,a,Or.inr ⟨h.2,h.1⟩⟩
  · exact Or.inl ⟨p,a,Or.inl ⟨h.2,h.1⟩⟩
  · exact Or.inr (Or.inl ⟨p,b,a,hy,hx⟩)
  · exact Or.inr (Or.inr ⟨q,p,ha.symm,hy,hx⟩)

theorem qmaRoutePort_even (p : ℕ → ℕ × ℕ) (k : ℕ) :
    qmaRoutePort p (2*k) = qmaDirectedPort (p k) (p (k-1)) := by
  simp [qmaRoutePort,qmaPortNeighborIndex]

theorem qmaRoutePort_odd (p : ℕ → ℕ × ℕ) (k : ℕ) :
    qmaRoutePort p (2*k+1) = qmaDirectedPort (p k) (p (k+1)) := by
  simp [qmaRoutePort,qmaPortNeighborIndex,Nat.add_div]

theorem qmaPortChain_link (p : ℕ → ℕ × ℕ) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (i : ℕ) (hi : i < 2*L+1) : QMAPortLink (qmaPortChain p L i) (qmaPortChain p L (i+1)) := by
  by_cases hi0 : i = 0
  · subst i
    rw [qmaPortChain_zero,qmaPortChain_inner p (by omega : 0 < 0+1) (by omega : 0+1 < 2*L+1)]
    have he := qmaRoutePort_odd p 0
    simp only [Nat.mul_zero,Nat.zero_add] at he
    rw [he]
    exact Or.inl ⟨p 0,qmaGridNeighborIndex (p 0) (p 1),Or.inl ⟨rfl,rfl⟩⟩
  by_cases hil : i = 2*L
  · subst i
    rw [qmaPortChain_last,qmaPortChain_inner p (by omega : 0 < 2*L) (by omega : 2*L < 2*L+1),
      qmaRoutePort_even]
    exact Or.inl ⟨p L,qmaGridNeighborIndex (p L) (p (L-1)),Or.inr ⟨rfl,rfl⟩⟩
  rw [qmaPortChain_inner p (by omega) hi,qmaPortChain_inner p (by omega : 0 < i+1) (by omega)]
  by_cases ho : i%2 = 1
  · have he : i = 2*(i/2)+1 := by omega
    rw [he,qmaRoutePort_odd]
    have hn : 2*(i/2)+1+1 = 2*(i/2+1) := by omega
    rw [hn,qmaRoutePort_even,Nat.add_sub_cancel]
    exact Or.inr (Or.inr ⟨p (i/2),p (i/2+1),hp _ (by omega),rfl,rfl⟩)
  · have he : i = 2*(i/2) := by omega
    rw [he,qmaRoutePort_even,qmaRoutePort_odd]
    exact Or.inr (Or.inl ⟨p (i/2),qmaGridNeighborIndex (p (i/2)) (p (i/2-1)),
      qmaGridNeighborIndex (p (i/2)) (p (i/2+1)),rfl,rfl⟩)

end ContinuumCoulomb

end OAI
