import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInflatedPath

namespace OAI

/-! Inflating a planar route family preserves its disjoint interiors. -/

namespace ContinuumCoulomb

theorem qmaInflatedPoint_avoids_vertex (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) (v : ℕ × ℕ)
    (hv : ∀ i, 0 < i → i < L → p i ≠ v) {k : ℕ} (hk0 : 0 < k) (hk : k < 8*L) :
    qmaInflatedPoint p k ≠ qmaLeafCenter v := by
  by_cases h0 : k%8 = 0
  · rw [qmaInflatedPoint_boundary p h0]
    intro h
    exact hv (k/8) (by omega) (by omega) (qmaLeafCenter_injective h)
  · exact qmaInflatedPoint_not_center p hpos hp hk.le h0 v

theorem qmaInflatedPoint_disjoint (p q : ℕ → ℕ × ℕ) {L M : ℕ}
    (hp0 : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hq0 : ∀ j ≤ M, 0 < (q j).1 ∧ 0 < (q j).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hq : ∀ j < M, qmaSquareGrid.Adj (q j) (q (j+1)))
    (hd : ∀ i j, 0 < i → i < L → j ≤ M → p i ≠ q j)
    (he : ∀ i j, i < L → j < M →
      ¬(p i = q j ∧ p (i+1) = q (j+1)) ∧ ¬(p i = q (j+1) ∧ p (i+1) = q j))
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 8*L) (hj : j ≤ 8*M) :
    qmaInflatedPoint p i ≠ qmaInflatedPoint q j := by
  intro h
  by_cases hiz : i%8 = 0
  · rw [qmaInflatedPoint_boundary p hiz] at h
    by_cases hjz : j%8 = 0
    · rw [qmaInflatedPoint_boundary q hjz] at h
      exact hd (i/8) (j/8) (by omega) (by omega) (by omega) (qmaLeafCenter_injective h)
    · exact qmaInflatedPoint_not_center q hq0 hq hj hjz _ h.symm
  · by_cases hjz : j%8 = 0
    · rw [qmaInflatedPoint_boundary q hjz] at h
      exact qmaInflatedPoint_not_center p hp0 hp hi.le hiz _ h
    have hid : i/8 < L := by omega
    have hjd : j/8 < M := by omega
    have hc := qmaScaledEdge_inner_collision (hp0 _ hid.le) (hq0 _ hjd.le)
      (hp _ hid) (hq _ hjd) (by omega : 0 < i%8) (Nat.mod_lt _ (by decide))
      (by omega : 0 < j%8) (Nat.mod_lt _ (by decide)) h
    exact hc.elim (he _ _ hid hjd).1 (he _ _ hid hjd).2

end ContinuumCoulomb

end OAI
