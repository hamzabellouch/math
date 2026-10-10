import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortLinks

namespace OAI

/-! A port-chain edge with both ends in the same cell is precisely one internal
route visit, with the incoming and outgoing directions in order. -/

namespace ContinuumCoulomb

theorem qmaPortChain_inner_pair (p : ℕ → ℕ × ℕ) {L k : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hk : k < 2*L+1) (q : ℕ × ℕ) (a b : Fin 4)
    (hl : qmaPortChain p L k = qmaGridPort q a)
    (hr : qmaPortChain p L (k+1) = qmaGridPort q b) :
    ∃ t, 0 < t ∧ t < L ∧ p t = q ∧
      qmaGridNeighborIndex (p t) (p (t-1)) = a ∧ qmaGridNeighborIndex (p t) (p (t+1)) = b := by
  have hk0 : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    subst k
    rw [qmaPortChain_zero] at hl
    exact qmaGridPort_ne_center q (p 0) a hl.symm
  have hkl : k+1 < 2*L+1 := by
    by_contra hn
    have he : k+1 = 2*L+1 := by omega
    rw [he,qmaPortChain_last] at hr
    exact qmaGridPort_ne_center q (p L) b hr.symm
  rw [qmaPortChain_inner p hk0 hk] at hl
  rw [qmaPortChain_inner p (by omega) hkl] at hr
  by_cases ho : k%2 = 1
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,qmaRoutePort_odd] at hl
    have he' : k+1 = 2*(k/2+1) := by omega
    rw [he',qmaRoutePort_even,Nat.add_sub_cancel] at hr
    have h1 : (p (k/2),qmaGridNeighborIndex (p (k/2)) (p (k/2+1))) = (q,a) :=
      qmaGridPort_injective hl
    have h2 : (p (k/2+1),qmaGridNeighborIndex (p (k/2+1)) (p (k/2))) = (q,b) :=
      qmaGridPort_injective hr
    have heq : p (k/2) = p (k/2+1) := (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm
    exact ((hp (k/2) (by omega)).ne heq).elim
  · have he : k = 2*(k/2) := by omega
    rw [he,qmaRoutePort_even] at hl
    rw [he,qmaRoutePort_odd] at hr
    have h1 : (p (k/2),qmaGridNeighborIndex (p (k/2)) (p (k/2-1))) = (q,a) :=
      qmaGridPort_injective hl
    have h2 : (p (k/2),qmaGridNeighborIndex (p (k/2)) (p (k/2+1))) = (q,b) :=
      qmaGridPort_injective hr
    exact ⟨k/2,by omega,by omega,congrArg Prod.fst h1,congrArg Prod.snd h1,congrArg Prod.snd h2⟩

end ContinuumCoulomb

end OAI
