import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumScaledDirection

namespace OAI

/-! Replace each unit edge of a simple path by its eight-step corridor. -/

namespace ContinuumCoulomb

def qmaInflatedPoint (p : ℕ → ℕ × ℕ) (k : ℕ) : ℕ × ℕ :=
  qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) (k%8)

@[simp] theorem qmaInflatedPoint_zero (p : ℕ → ℕ × ℕ) :
    qmaInflatedPoint p 0 = qmaLeafCenter (p 0) := by simp [qmaInflatedPoint]

theorem qmaInflatedPoint_boundary (p : ℕ → ℕ × ℕ) {k : ℕ} (hk : k%8 = 0) :
    qmaInflatedPoint p k = qmaLeafCenter (p (k/8)) := by
  simp only [qmaInflatedPoint,hk,qmaManhattanPoint_zero]

@[simp] theorem qmaInflatedPoint_last (p : ℕ → ℕ × ℕ) (L : ℕ) :
    qmaInflatedPoint p (8*L) = qmaLeafCenter (p L) := by
  simp [qmaInflatedPoint]

theorem qmaLeafCenter_injective : Function.Injective qmaLeafCenter := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp only [qmaLeafCenter] at hx hy <;> omega

theorem qmaInflatedPoint_step (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) {k : ℕ} (hk : k < 8*L) :
    qmaSquareGrid.Adj (qmaInflatedPoint p k) (qmaInflatedPoint p (k+1)) := by
  have hdiv : k/8 < L := by omega
  have hlen := qmaLeafCenter_adj_length (hp _ hdiv)
  have hm : k%8 < 8 := Nat.mod_lt _ (by decide)
  by_cases h7 : k%8 = 7
  · have hq : (k+1)/8 = k/8+1 := by omega
    have hr : (k+1)%8 = 0 := by omega
    have hs := qmaManhattanPoint_adj (qmaLeafCenter (p (k/8)))
      (qmaLeafCenter (p (k/8+1))) 7 (by omega)
    have he := qmaManhattanPoint_last (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1)))
    rw [hlen] at he
    change qmaSquareGrid.Adj
      (qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) 7)
      (qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) 8) at hs
    rw [he] at hs
    simpa only [qmaInflatedPoint,h7,hq,hr,qmaManhattanPoint_zero] using hs
  · have hq : (k+1)/8 = k/8 := by omega
    have hr : (k+1)%8 = k%8+1 := by omega
    simpa only [qmaInflatedPoint,hq,hr] using
      qmaManhattanPoint_adj (qmaLeafCenter (p (k/8)))
        (qmaLeafCenter (p (k/8+1))) (k%8) (by omega)

theorem qmaInflatedPoint_gridline (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) {k : ℕ} (hk : k ≤ 8*L) :
    (qmaInflatedPoint p k).1%8 = 4 ∨ (qmaInflatedPoint p k).2%8 = 4 := by
  by_cases h0 : k%8 = 0
  · rw [qmaInflatedPoint_boundary p h0]
    left
    simp [qmaLeafCenter,Nat.add_mod]
  · have hdiv : k/8 < L := by omega
    have hlen := qmaLeafCenter_adj_length (hp _ hdiv)
    exact qmaLeafCenter_point_gridline _ _ _ (by omega)

theorem qmaInflatedPoint_not_center (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) {k : ℕ}
    (hk : k ≤ 8*L) (h0 : k%8 ≠ 0) (r : ℕ × ℕ) :
    qmaInflatedPoint p k ≠ qmaLeafCenter r := by
  have hdiv : k/8 < L := by omega
  obtain ⟨a,ha⟩ := qmaGridNeighbor_exists (hp _ hdiv)
  change qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) (k%8) ≠ _
  rw [← ha,qmaScaledDirectionPoint_eq _ (hpos _ hdiv.le).1 (hpos _ hdiv.le).2 a
    (Nat.le_of_lt (Nat.mod_lt _ (by decide)))]
  exact qmaScaledDirectionPoint_not_center _ r a
    (by omega) (Nat.mod_lt _ (by decide))

theorem qmaInflatedPoint_injective (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hs : ∀ i j, i ≤ L → j ≤ L → p i = p j → i = j)
    {i j : ℕ} (hi : i ≤ 8*L) (hj : j ≤ 8*L)
    (h : qmaInflatedPoint p i = qmaInflatedPoint p j) : i = j := by
  by_cases hi0 : i%8 = 0
  · rw [qmaInflatedPoint_boundary p hi0] at h
    by_cases hj0 : j%8 = 0
    · rw [qmaInflatedPoint_boundary p hj0] at h
      have he := hs (i/8) (j/8) (by omega) (by omega) (qmaLeafCenter_injective h)
      omega
    · exact (qmaInflatedPoint_not_center p hpos hp hj hj0 _ h.symm).elim
  · by_cases hj0 : j%8 = 0
    · rw [qmaInflatedPoint_boundary p hj0] at h
      exact (qmaInflatedPoint_not_center p hpos hp hi hi0 _ h).elim
    have hid : i/8 < L := by omega
    have hjd : j/8 < L := by omega
    have hip : 0 < i%8 := by omega
    have hjp : 0 < j%8 := by omega
    have hi8 := Nat.mod_lt i (by decide : 0 < 8)
    have hj8 := Nat.mod_lt j (by decide : 0 < 8)
    have hc := qmaScaledEdge_inner_collision (hpos _ hid.le) (hpos _ hjd.le)
      (hp _ hid) (hp _ hjd) hip hi8 hjp hj8 h
    rcases hc with ⟨ha,_⟩ | ⟨ha,hb⟩
    · have hd := hs (i/8) (j/8) hid.le hjd.le ha
      have hlen := qmaLeafCenter_adj_length (hp (i/8) hid)
      change qmaManhattanPoint (qmaLeafCenter (p (i/8))) (qmaLeafCenter (p (i/8+1))) (i%8) =
        qmaManhattanPoint (qmaLeafCenter (p (j/8))) (qmaLeafCenter (p (j/8+1))) (j%8) at h
      rw [← hd] at h
      have hm1 := qmaManhattanPoint_distance (qmaLeafCenter (p (i/8)))
        (qmaLeafCenter (p (i/8+1))) (i%8) (by omega)
      have hm2 := qmaManhattanPoint_distance (qmaLeafCenter (p (i/8)))
        (qmaLeafCenter (p (i/8+1))) (j%8) (by omega)
      rw [h] at hm1
      omega
    · have hd1 := hs (i/8) (j/8+1) hid.le (by omega) ha
      have hd2 := hs (i/8+1) (j/8) (by omega) hjd.le hb
      omega

end ContinuumCoulomb

end OAI
