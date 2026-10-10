import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanSupport

namespace OAI

/-! Three disjoint local arms joining a degree-three vertex to ordered lane ports. -/

namespace ContinuumCoulomb

def qmaFanoutSupport (c : Fin 3 → ℕ) (a : Fin 3) (p : ℕ × ℕ) : Prop :=
  if a = 0 then
    (p.2 = 2 ∧ 2 ≤ p.1 ∧ p.1 ≤ c 0+3) ∨
      (p.1 = c 0+3 ∧ 2 ≤ p.2 ∧ p.2 ≤ c 0+3)
  else if a = 1 then
    (p.1 = 2 ∧ 2 ≤ p.2 ∧ p.2 ≤ c 1+3) ∨
      (p.2 = c 1+3 ∧ 2 ≤ p.1 ∧ p.1 ≤ c 1+3)
  else
    (p.2 = 2 ∧ 1 ≤ p.1 ∧ p.1 ≤ 2) ∨
    (p.1 = 1 ∧ 2 ≤ p.2 ∧ p.2 ≤ c 2+4) ∨
    (p.2 = c 2+4 ∧ 1 ≤ p.1 ∧ p.1 ≤ c 2+3) ∨
    (p.1 = c 2+3 ∧ c 2+3 ≤ p.2 ∧ p.2 ≤ c 2+4)

def qmaFanoutPort (c : Fin 3 → ℕ) (a : Fin 3) : ℕ × ℕ := (c a+3,c a+3)

theorem qmaFanout_center (c : Fin 3 → ℕ) (a : Fin 3) : qmaFanoutSupport c a (2,2) := by
  fin_cases a <;> simp [qmaFanoutSupport]

theorem qmaFanout_port (c : Fin 3 → ℕ) (a : Fin 3) : qmaFanoutSupport c a (qmaFanoutPort c a) := by
  fin_cases a <;> simp [qmaFanoutSupport,qmaFanoutPort]

theorem qmaFanout_only_center (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    {a b : Fin 3} (hab : a ≠ b) {p : ℕ × ℕ}
    (ha : qmaFanoutSupport c a p) (hb : qmaFanoutSupport c b p) : p = (2,2) := by
  rcases p with ⟨x,y⟩
  fin_cases a <;> fin_cases b <;> simp [qmaFanoutSupport] at ha hb hab ⊢ <;> omega

theorem qmaFanout_bounded (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    (a : Fin 3) {p : ℕ × ℕ} (hp : qmaFanoutSupport c a p) :
    1 ≤ p.1 ∧ p.1 ≤ c 2+4 ∧ 2 ≤ p.2 ∧ p.2 ≤ c 2+4 := by
  fin_cases a <;> simp [qmaFanoutSupport] at hp <;> omega

theorem qmaFanout_other_port (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    {a b : Fin 3} (hab : a ≠ b) : ¬qmaFanoutSupport c a (qmaFanoutPort c b) := by
  intro h
  have he := qmaFanout_only_center c h01 h12 hab h (qmaFanout_port c b)
  have hx := congrArg Prod.fst he
  dsimp [qmaFanoutPort] at hx
  omega

end ContinuumCoulomb

end OAI
