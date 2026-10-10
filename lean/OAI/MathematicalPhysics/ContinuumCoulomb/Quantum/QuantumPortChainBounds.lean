import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChain

namespace OAI

/-! Uniform rectangular bounds for the complete port-chain construction. -/

namespace ContinuumCoulomb

theorem qmaExpandedPoint_bounds {p : ℕ × ℕ} {X Y : ℕ}
    (hx : p.1 < X) (hy : p.2 < Y) :
    (qmaExpandedPoint p).1 < 32*X ∧ (qmaExpandedPoint p).2 < 32*Y := by
  dsimp [qmaExpandedPoint]
  omega

theorem qmaPortChain_bounds (p : ℕ → ℕ × ℕ) {L X Y : ℕ}
    (hp : ∀ i ≤ L, (p i).1 < X ∧ (p i).2 < Y)
    (k : ℕ) (hk : k ≤ 2*L+1) :
    (qmaPortChain p L k).1 < 32*X ∧ (qmaPortChain p L k).2 < 32*Y := by
  by_cases hk0 : k = 0
  · subst k
    rw [qmaPortChain_zero]
    exact qmaExpandedPoint_bounds (hp 0 (Nat.zero_le _)).1 (hp 0 (Nat.zero_le _)).2
  by_cases hkL : k = 2*L+1
  · subst k
    rw [qmaPortChain_last]
    exact qmaExpandedPoint_bounds (hp L le_rfl).1 (hp L le_rfl).2
  rw [qmaPortChain_inner p (by omega) (by omega)]
  exact qmaGridPort_bounds (hp (k/2) (by omega)).1 (hp (k/2) (by omega)).2 _

end ContinuumCoulomb

end OAI
