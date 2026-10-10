import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteLeaf
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighborsFour
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanSupport

namespace OAI

/-! Eightfold unit-edge corridors leave the diagonal leaf sites free. -/

namespace ContinuumCoulomb

theorem qmaLeafCenter_length (p q : ℕ × ℕ) :
    qmaManhattanLength (qmaLeafCenter p) (qmaLeafCenter q) = 8*qmaManhattanLength p q := by
  simp only [qmaManhattanLength,qmaLeafCenter,Nat.dist_add_add_right,Nat.dist_mul_left,Nat.mul_add]

theorem qmaLeafCenter_adj_length {p q : ℕ × ℕ} (h : qmaSquareGrid.Adj p q) :
    qmaManhattanLength (qmaLeafCenter p) (qmaLeafCenter q) = 8 := by
  rw [qmaLeafCenter_length]
  change qmaManhattanLength p q = 1 at h
  omega

theorem qmaLeafCenter_point_gridline (p q : ℕ × ℕ) (k : ℕ)
    (hk : k ≤ qmaManhattanLength (qmaLeafCenter p) (qmaLeafCenter q)) :
    (qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) k).1%8 = 4 ∨
      (qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) k).2%8 = 4 := by
  have h := qmaManhattanPoint_support (qmaLeafCenter p) (qmaLeafCenter q) k hk
  rcases h with ⟨hy,_⟩ | ⟨hx,_⟩
  · right
    rw [hy]
    simp [qmaLeafCenter,Nat.add_mod]
  · left
    rw [hx]
    simp [qmaLeafCenter,Nat.add_mod]

theorem qmaRouteLeaf_avoids_corridor (p q r : ℕ × ℕ) (a : Fin 4) (k : ℕ)
    (hk : k ≤ qmaManhattanLength (qmaLeafCenter q) (qmaLeafCenter r)) :
    qmaRouteLeaf p a ≠ qmaManhattanPoint (qmaLeafCenter q) (qmaLeafCenter r) k :=
  qmaRouteLeaf_avoids p _ a (qmaLeafCenter_point_gridline q r k hk)

theorem qmaLeafCenter_point_one (p : ℕ × ℕ) (hx : 0 < p.1) (hy : 0 < p.2) (a : Fin 4) :
    qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter (qmaGridNeighbor p a)) 1 = qmaLeafFirst p a := by
  have hpx : p.1-1+1 = p.1 := by omega
  have hpy : p.2-1+1 = p.2 := by omega
  fin_cases a <;> simp [qmaManhattanPoint,qmaAxisWalk,qmaLeafCenter,qmaGridNeighbor,qmaLeafFirst,Nat.dist]
  all_goals first | omega | (split_ifs <;> simp only [Prod.mk.injEq] <;> omega)

theorem qmaLeafCenter_point_first {p q : ℕ × ℕ} (hx : 0 < p.1) (hy : 0 < p.2)
    (ha : qmaSquareGrid.Adj p q) :
    qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) 1 =
      qmaLeafFirst p (qmaGridNeighborIndex p q) := by
  simpa only [qmaGridNeighborIndex_spec hx hy ha] using
    qmaLeafCenter_point_one p hx hy (qmaGridNeighborIndex p q)

end ContinuumCoulomb

end OAI
