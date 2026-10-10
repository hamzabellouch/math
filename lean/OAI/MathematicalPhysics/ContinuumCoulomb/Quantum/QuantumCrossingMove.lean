import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInnerPorts

namespace OAI

/-! Moving only crossing-cell ports is injective on all original spin locations. -/

namespace ContinuumCoulomb

def QMAPortPoint (z : ℕ × ℕ) : Prop :=
  (∃ p, z = qmaExpandedPoint p) ∨ ∃ p a, z = qmaGridPort p a

theorem qmaCrossingMove_injective (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    {x y : ℕ × ℕ} (hx : QMAPortPoint x) (hy : QMAPortPoint y)
    (h : qmaCrossingMove cross x = qmaCrossingMove cross y) : x = y := by
  rcases hx with ⟨p,rfl⟩ | ⟨p,a,rfl⟩ <;> rcases hy with ⟨q,rfl⟩ | ⟨q,b,rfl⟩
  · simpa only [qmaCrossingMove_center] using h
  · simp only [qmaCrossingMove_center,qmaCrossingMove_port] at h
    by_cases hq : cross q
    · rw [ite_eq_left hq] at h
      exact (qmaInnerPort_ne_center q p b h.symm).elim
    · rw [ite_eq_right hq] at h
      exact (qmaGridPort_ne_center q p b h.symm).elim
  · simp only [qmaCrossingMove_center,qmaCrossingMove_port] at h
    by_cases hp : cross p
    · rw [ite_eq_left hp] at h
      exact (qmaInnerPort_ne_center p q a h).elim
    · rw [ite_eq_right hp] at h
      exact (qmaGridPort_ne_center p q a h).elim
  · simp only [qmaCrossingMove_port] at h
    by_cases hp : cross p <;> by_cases hq : cross q
    · rw [ite_eq_left hp,ite_eq_left hq] at h
      have he : (p,a) = (q,b) := qmaInnerPort_injective h
      exact congrArg (fun z : (ℕ × ℕ) × Fin 4 => qmaGridPort z.1 z.2) he
    · rw [ite_eq_left hp,ite_eq_right hq] at h
      exact (qmaInnerPort_ne_port p q a b h).elim
    · rw [ite_eq_right hp,ite_eq_left hq] at h
      exact (qmaInnerPort_ne_port q p b a h.symm).elim
    · simpa only [ite_eq_right hp,ite_eq_right hq] using h

theorem qmaGadgetAncilla_ne_moved (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 2) {x : ℕ × ℕ} (hx : QMAPortPoint x) :
    qmaGadgetAncilla p a ≠ qmaCrossingMove cross x := by
  rcases hx with ⟨q,rfl⟩ | ⟨q,b,rfl⟩
  · rw [qmaCrossingMove_center]
    exact qmaGadgetAncilla_ne_center p q a
  · rw [qmaCrossingMove_port]
    split_ifs
    · exact qmaGadgetAncilla_ne_inner p q a b
    · exact qmaGadgetAncilla_ne_port p q a b

end ContinuumCoulomb

end OAI
