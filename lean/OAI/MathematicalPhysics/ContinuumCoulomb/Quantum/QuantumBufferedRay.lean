import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedFanout

namespace OAI

/-! A direction choice keeps each endpoint arm disjoint from its own outgoing ray. -/

namespace ContinuumCoulomb

def qmaBufferedRay (u : ℕ) (vertical positive : Bool) (z : ℕ × ℕ) : Prop :=
  if vertical then z.1 = u ∧ (if positive then u ≤ z.2 else z.2 ≤ u)
  else z.2 = u ∧ (if positive then u ≤ z.1 else z.1 ≤ u)

def qmaBufferedRaySide (a : Fin 3) (vertical positive : Bool) : Bool :=
  if vertical = (a == 1) then !positive else false

theorem qmaBufferedFanout_ray (c : Fin 3 → ℕ) (side : Fin 3 → Bool)
    (a : Fin 3) (vertical positive : Bool)
    (hs : side a = qmaBufferedRaySide a vertical positive)
    (hd : a ≠ 2 ∨ vertical = true ∨ positive = true) {z : ℕ × ℕ}
    (ha : qmaBufferedFanoutSupport c side a z)
    (hr : qmaBufferedRay (qmaBufferedPort c a) vertical positive z) :
    z = (qmaBufferedPort c a,qmaBufferedPort c a) := by
  rcases z with ⟨x,y⟩
  cases vertical <;> cases positive <;> fin_cases a <;>
    simp [qmaBufferedRaySide] at hs <;>
    simp [qmaBufferedFanoutSupport,qmaBufferedRay,qmaBufferedOffset,
      qmaBufferedPort,qmaBetween,hs] at ha hr hd ⊢ <;> omega

end ContinuumCoulomb

end OAI
