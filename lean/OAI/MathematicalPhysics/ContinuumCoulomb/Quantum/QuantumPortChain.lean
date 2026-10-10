import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridPorts

namespace OAI

/-! Each coarse route is replaced by its ordered incoming and outgoing cell ports. -/

namespace ContinuumCoulomb

def qmaPortNeighborIndex (k : ℕ) : ℕ := if k%2 = 1 then k/2+1 else k/2-1

def qmaRoutePort (p : ℕ → ℕ × ℕ) (k : ℕ) : ℕ × ℕ :=
  qmaDirectedPort (p (k/2)) (p (qmaPortNeighborIndex k))

def qmaPortChain (p : ℕ → ℕ × ℕ) (L k : ℕ) : ℕ × ℕ :=
  if k = 0 then qmaExpandedPoint (p 0) else
    if k = 2*L+1 then qmaExpandedPoint (p L) else qmaRoutePort p k

@[simp] theorem qmaPortChain_zero (p : ℕ → ℕ × ℕ) (L : ℕ) :
    qmaPortChain p L 0 = qmaExpandedPoint (p 0) := by simp [qmaPortChain]

@[simp] theorem qmaPortChain_last (p : ℕ → ℕ × ℕ) (L : ℕ) :
    qmaPortChain p L (2*L+1) = qmaExpandedPoint (p L) := by simp [qmaPortChain]

theorem qmaPortChain_inner (p : ℕ → ℕ × ℕ) {L k : ℕ} (hk0 : 0 < k) (hk : k < 2*L+1) :
    qmaPortChain p L k = qmaRoutePort p k := by
  simp [qmaPortChain,show k ≠ 0 from by omega,show k ≠ 2*L+1 from by omega]

theorem qmaPortNeighborIndex_bounds {L k : ℕ} (_hk0 : 0 < k) (hk : k < 2*L+1) :
    k/2 ≤ L ∧ qmaPortNeighborIndex k ≤ L := by
  unfold qmaPortNeighborIndex
  split_ifs <;> omega

theorem qmaPortNeighborIndex_injective {L i j : ℕ} (hi0 : 0 < i) (_hi : i < 2*L+1)
    (hj0 : 0 < j) (_hj : j < 2*L+1) (hd : i/2 = j/2)
    (hn : qmaPortNeighborIndex i = qmaPortNeighborIndex j) : i = j := by
  unfold qmaPortNeighborIndex at hn
  split_ifs at hn <;> omega

theorem qmaRoutePort_adjacent (p : ℕ → ℕ × ℕ) {L k : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) (hk0 : 0 < k) (hk : k < 2*L+1) :
    qmaSquareGrid.Adj (p (k/2)) (p (qmaPortNeighborIndex k)) := by
  by_cases h : k%2 = 1
  · simp only [qmaPortNeighborIndex,h,ite_true]
    exact hp (k/2) (by omega)
  · simp only [qmaPortNeighborIndex,h,ite_false]
    have he : k/2-1+1 = k/2 := by omega
    have ha := hp (k/2-1) (by omega)
    rw [he] at ha
    exact ha.symm

theorem qmaPortChain_inner_not_center (p : ℕ → ℕ × ℕ) {L k : ℕ}
    (hk0 : 0 < k) (hk : k < 2*L+1) (q : ℕ × ℕ) : qmaPortChain p L k ≠ qmaExpandedPoint q := by
  rw [qmaPortChain_inner p hk0 hk]
  exact qmaGridPort_ne_center _ _ _

theorem qmaPortChain_inner_injective (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hs : ∀ i j, i ≤ L → j ≤ L → p i = p j → i = j)
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 2*L+1) (hj0 : 0 < j) (hj : j < 2*L+1)
    (h : qmaPortChain p L i = qmaPortChain p L j) : i = j := by
  rw [qmaPortChain_inner p hi0 hi,qmaPortChain_inner p hj0 hj] at h
  obtain ⟨hiB,hiN⟩ := qmaPortNeighborIndex_bounds hi0 hi
  obtain ⟨hjB,hjN⟩ := qmaPortNeighborIndex_bounds hj0 hj
  have he := qmaDirectedPort_injective (hpos _ hiB) (hpos _ hjB)
    (qmaRoutePort_adjacent p hp hi0 hi) (qmaRoutePort_adjacent p hp hj0 hj) h
  exact qmaPortNeighborIndex_injective hi0 hi hj0 hj (hs _ _ hiB hjB he.1) (hs _ _ hiN hjN he.2)

end ContinuumCoulomb

end OAI
