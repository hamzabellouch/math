import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHalfCorridor

namespace OAI

/-! Cell-local paths translate injectively and different cells are disjoint. -/

namespace ContinuumCoulomb

def qmaCellTranslate (p z : ℕ × ℕ) : ℕ × ℕ := (32*p.1+z.1,32*p.2+z.2)

theorem qmaCellTranslate_injective (p : ℕ × ℕ) : Function.Injective (qmaCellTranslate p) := by
  intro x y h
  exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
    (Nat.add_left_cancel (congrArg Prod.snd h))

theorem qmaCellTranslate_cell (p z : ℕ × ℕ) (hz : z.1 < 32 ∧ z.2 < 32) :
    ((qmaCellTranslate p z).1/32,(qmaCellTranslate p z).2/32) = p := by
  apply Prod.ext <;> dsimp [qmaCellTranslate] <;> omega

theorem qmaCellTranslate_unique {p q x y : ℕ × ℕ}
    (hx : x.1 < 32 ∧ x.2 < 32) (hy : y.1 < 32 ∧ y.2 < 32)
    (h : qmaCellTranslate p x = qmaCellTranslate q y) : p = q ∧ x = y := by
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  rw [qmaCellTranslate_cell p x hx,qmaCellTranslate_cell q y hy] at he
  subst q
  exact ⟨rfl,qmaCellTranslate_injective p h⟩

theorem qmaCellTranslate_step (p x y : ℕ × ℕ) :
    Nat.dist (qmaCellTranslate p x).1 (qmaCellTranslate p y).1+
      Nat.dist (qmaCellTranslate p x).2 (qmaCellTranslate p y).2 =
        Nat.dist x.1 y.1+Nat.dist x.2 y.2 := by
  simp only [qmaCellTranslate,Nat.dist_add_add_left]

theorem qmaCellTranslate_port (p : ℕ × ℕ) (a : Fin 4) :
    qmaCellTranslate p (qmaCellPort a) = qmaGridPort p a := by
  fin_cases a <;> rfl

theorem qmaCellTranslate_inner (p : ℕ × ℕ) (a : Fin 4) :
    qmaCellTranslate p (qmaInnerPort (0,0) a) = qmaInnerPort p a := by
  fin_cases a <;> rfl

theorem qmaCellTranslate_patch (p z : ℕ × ℕ) :
    qmaCellTranslate p (10+z.1,10+z.2) = qmaPatchTranslate p z := by
  simp only [qmaCellTranslate,qmaPatchTranslate,Nat.add_assoc]

end ContinuumCoulomb

end OAI
