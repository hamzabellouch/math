import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedArms

namespace OAI

/-! An arm can overlap a grid-aligned unit edge only at its terminal grid point. -/

namespace ContinuumCoulomb

theorem qmaBufferedFanout_horizontal_grid_edge (c : Fin 3 → ℕ) (a : Fin 3)
    {p q : ℕ × ℕ} (hp : qmaBufferedFanoutSupport c (fun _ => false) a p)
    (hq : qmaBufferedFanoutSupport c (fun _ => false) a q)
    (hy : p.2 = q.2) (hm : p.2 % 8 = 0) (hd : Nat.dist p.1 q.1 = 1) :
    p.1 % 8 = 0 ∨ q.1 % 8 = 0 := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  fin_cases a <;>
    simp [qmaBufferedFanoutSupport,qmaBufferedOffset,qmaBufferedPort,qmaBetween,Nat.dist] at * <;> omega

theorem qmaBufferedFanout_vertical_grid_edge (c : Fin 3 → ℕ) (a : Fin 3)
    {p q : ℕ × ℕ} (hp : qmaBufferedFanoutSupport c (fun _ => false) a p)
    (hq : qmaBufferedFanoutSupport c (fun _ => false) a q)
    (hx : p.1 = q.1) (hm : p.1 % 8 = 0) (hd : Nat.dist p.2 q.2 = 1) :
    p.2 % 8 = 0 ∨ q.2 % 8 = 0 := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  fin_cases a <;>
    simp [qmaBufferedFanoutSupport,qmaBufferedOffset,qmaBufferedPort,qmaBetween,Nat.dist] at * <;> omega

end ContinuumCoulomb

end OAI
