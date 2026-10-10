import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChain

namespace OAI

/-! Port chains are simple and remain disjoint even where coarse routes meet. -/

namespace ContinuumCoulomb

theorem qmaPortChain_injective (p : ℕ → ℕ × ℕ) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hs : ∀ i j, i ≤ L → j ≤ L → p i = p j → i = j)
    {i j : ℕ} (hi : i ≤ 2*L+1) (hj : j ≤ 2*L+1)
    (h : qmaPortChain p L i = qmaPortChain p L j) : i = j := by
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · exact hj0.symm
    by_cases hjL : j = 2*L+1
    · subst j
      rw [qmaPortChain_zero,qmaPortChain_last] at h
      have hz := hs 0 L (Nat.zero_le _) le_rfl (qmaExpandedPoint_injective h)
      omega
    · simp only [qmaPortChain_zero] at h
      exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h.symm).elim
  by_cases hiL : i = 2*L+1
  · subst i
    by_cases hj0 : j = 0
    · subst j
      rw [qmaPortChain_zero,qmaPortChain_last] at h
      have hz := hs L 0 le_rfl (Nat.zero_le _) (qmaExpandedPoint_injective h)
      omega
    by_cases hjL : j = 2*L+1
    · exact hjL.symm
    · simp only [qmaPortChain_last] at h
      exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h.symm).elim
  by_cases hj0 : j = 0
  · subst j
    simp only [qmaPortChain_zero] at h
    exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h).elim
  by_cases hjL : j = 2*L+1
  · subst j
    simp only [qmaPortChain_last] at h
    exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h).elim
  exact qmaPortChain_inner_injective p hp hpos hs (by omega) (by omega) (by omega) (by omega) h

theorem qmaPortChain_interiors_disjoint (p q : ℕ → ℕ × ℕ) {L M : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hq : ∀ i < M, qmaSquareGrid.Adj (q i) (q (i+1)))
    (hp0 : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hq0 : ∀ j ≤ M, 0 < (q j).1 ∧ 0 < (q j).2)
    (he : ∀ i j, i < L → j < M →
      ¬(p i = q j ∧ p (i+1) = q (j+1)) ∧ ¬(p i = q (j+1) ∧ p (i+1) = q j))
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 2*L+1) (hj : j ≤ 2*M+1) :
    qmaPortChain p L i ≠ qmaPortChain q M j := by
  intro h
  by_cases hj0 : j = 0
  · subst j
    simp only [qmaPortChain_zero] at h
    exact (qmaPortChain_inner_not_center p hi0 hi _ h).elim
  by_cases hjM : j = 2*M+1
  · subst j
    simp only [qmaPortChain_last] at h
    exact (qmaPortChain_inner_not_center p hi0 hi _ h).elim
  have hj' : j < 2*M+1 := by omega
  rw [qmaPortChain_inner p hi0 hi,qmaPortChain_inner q (by omega) hj'] at h
  obtain ⟨hib,_⟩ := qmaPortNeighborIndex_bounds hi0 hi
  obtain ⟨hjb,_⟩ := qmaPortNeighborIndex_bounds (by omega : 0 < j) hj'
  have hc := qmaDirectedPort_injective (hp0 _ hib) (hq0 _ hjb)
    (qmaRoutePort_adjacent p hp hi0 hi) (qmaRoutePort_adjacent q hq (by omega) hj') h
  by_cases hie : i%2 = 1 <;> by_cases hje : j%2 = 1
  · simp only [qmaPortNeighborIndex,hie,hje,ite_true] at hc
    exact (he (i/2) (j/2) (by omega) (by omega)).1 hc
  · simp only [qmaPortNeighborIndex,hie,hje,ite_true,ite_false] at hc
    have hjp : j/2-1+1 = j/2 := by omega
    apply (he (i/2) (j/2-1) (by omega) (by omega)).2
    simpa only [hjp] using hc
  · simp only [qmaPortNeighborIndex,hie,hje,ite_true,ite_false] at hc
    have hip : i/2-1+1 = i/2 := by omega
    apply (he (i/2-1) (j/2) (by omega) (by omega)).2
    simpa only [hip] using And.intro hc.2 hc.1
  · simp only [qmaPortNeighborIndex,hie,hje,ite_false] at hc
    have hip : i/2-1+1 = i/2 := by omega
    have hjp : j/2-1+1 = j/2 := by omega
    apply (he (i/2-1) (j/2-1) (by omega) (by omega)).1
    simpa only [hip,hjp] using And.intro hc.2 hc.1

end ContinuumCoulomb

end OAI
