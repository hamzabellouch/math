import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFanoutPorts

namespace OAI

/-! Endpoint arms offset from all global grid lines, with a one-step terminal join. -/

namespace ContinuumCoulomb

def qmaBufferedPort (c : Fin 3 → ℕ) (a : Fin 3) : ℕ := 8*(c a+3)
def qmaBufferedOffset (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) : ℕ :=
  if side a then qmaBufferedPort c a+1 else qmaBufferedPort c a-1

theorem qmaBufferedOffset_bounds (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedPort c a ≤ qmaBufferedOffset c side a+1 ∧
      qmaBufferedOffset c side a ≤ qmaBufferedPort c a+1 := by
  unfold qmaBufferedOffset
  split_ifs <;> omega

theorem qmaBufferedOffset_not_grid (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (u : ℕ) :
    qmaBufferedOffset c side a ≠ 8*u := by
  unfold qmaBufferedOffset qmaBufferedPort
  split_ifs <;> omega

def qmaBufferedFanoutSupport (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (p : ℕ × ℕ) : Prop :=
  if a = 0 then
    (p.2 = 17 ∧ 17 ≤ p.1 ∧ p.1 ≤ qmaBufferedOffset c side 0) ∨
    (p.1 = qmaBufferedOffset c side 0 ∧ 17 ≤ p.2 ∧ p.2 ≤ qmaBufferedPort c 0) ∨
    (p.2 = qmaBufferedPort c 0 ∧ qmaBetween (qmaBufferedOffset c side 0) (qmaBufferedPort c 0) p.1)
  else if a = 1 then
    (p.1 = 17 ∧ 17 ≤ p.2 ∧ p.2 ≤ qmaBufferedOffset c side 1) ∨
    (p.2 = qmaBufferedOffset c side 1 ∧ 17 ≤ p.1 ∧ p.1 ≤ qmaBufferedPort c 1) ∨
    (p.1 = qmaBufferedPort c 1 ∧ qmaBetween (qmaBufferedOffset c side 1) (qmaBufferedPort c 1) p.2)
  else
    (p.2 = 17 ∧ 9 ≤ p.1 ∧ p.1 ≤ 17) ∨
    (p.1 = 9 ∧ 17 ≤ p.2 ∧ p.2 ≤ 8*(c 2+4)+1) ∨
    (p.2 = 8*(c 2+4)+1 ∧ 9 ≤ p.1 ∧ p.1 ≤ qmaBufferedOffset c side 2) ∨
    (p.1 = qmaBufferedOffset c side 2 ∧ qmaBufferedPort c 2 ≤ p.2 ∧ p.2 ≤ 8*(c 2+4)+1) ∨
    (p.2 = qmaBufferedPort c 2 ∧ qmaBetween (qmaBufferedOffset c side 2) (qmaBufferedPort c 2) p.1)

theorem qmaBufferedFanout_center (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedFanoutSupport c side a (17,17) := by
  have h := qmaBufferedOffset_bounds c side a
  fin_cases a <;> simp [qmaBufferedFanoutSupport] <;> dsimp [qmaBufferedPort] at h <;> omega

theorem qmaBufferedFanout_port (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedFanoutSupport c side a (qmaBufferedPort c a,qmaBufferedPort c a) := by
  fin_cases a <;> simp [qmaBufferedFanoutSupport,qmaBetween]

theorem qmaBufferedFanout_only_center (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    (side : Fin 3 → Bool) {a b : Fin 3} (hab : a ≠ b) {p : ℕ × ℕ}
    (ha : qmaBufferedFanoutSupport c side a p) (hb : qmaBufferedFanoutSupport c side b p) : p = (17,17) := by
  have h0 := qmaBufferedOffset_bounds c side 0
  have h1 := qmaBufferedOffset_bounds c side 1
  have h2 := qmaBufferedOffset_bounds c side 2
  dsimp [qmaBufferedPort] at h0 h1 h2
  rcases p with ⟨x,y⟩
  fin_cases a <;> fin_cases b <;>
    simp [qmaBufferedFanoutSupport,qmaBufferedPort,qmaBetween] at ha hb hab ⊢ <;> omega

theorem qmaBufferedFanout_grid_point (c : Fin 3 → ℕ) (side : Fin 3 → Bool)
    (a : Fin 3) (u v : ℕ) (h : qmaBufferedFanoutSupport c side a (8*u,8*v)) :
    (8*u,8*v) = (qmaBufferedPort c a,qmaBufferedPort c a) := by
  have h0 := qmaBufferedOffset_bounds c side 0
  have h1 := qmaBufferedOffset_bounds c side 1
  have h2 := qmaBufferedOffset_bounds c side 2
  have h0x := qmaBufferedOffset_not_grid c side 0 u
  have h1y := qmaBufferedOffset_not_grid c side 1 v
  have h2x := qmaBufferedOffset_not_grid c side 2 u
  dsimp [qmaBufferedPort] at h0 h1 h2 ⊢
  fin_cases a <;> simp [qmaBufferedFanoutSupport,qmaBufferedPort,qmaBetween] at h ⊢ <;> omega

theorem qmaBufferedStub_avoids_outgoing (c : Fin 3 → ℕ) (side : Fin 3 → Bool)
    (a : Fin 3) (x : ℕ)
    (hx : qmaBetween (qmaBufferedOffset c side a) (qmaBufferedPort c a) x)
    (hout : if side a then x ≤ qmaBufferedPort c a else qmaBufferedPort c a ≤ x) :
    x = qmaBufferedPort c a := by
  unfold qmaBufferedOffset qmaBetween at hx
  split_ifs at hx hout <;> omega

end ContinuumCoulomb

end OAI
