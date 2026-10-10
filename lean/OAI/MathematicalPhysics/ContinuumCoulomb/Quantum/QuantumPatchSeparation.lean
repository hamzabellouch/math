import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteLanes

namespace OAI

/-! Disjoint twelve-wide crossing patches after a fixed integer expansion. -/

namespace ContinuumCoulomb

def qmaExpandedPoint (p : ℕ × ℕ) : ℕ × ℕ := (32*p.1+16,32*p.2+16)
def qmaPatchBox (p : ℕ × ℕ) : Set (ℕ × ℕ) :=
  {z | Nat.dist z.1 (qmaExpandedPoint p).1 ≤ 6 ∧ Nat.dist z.2 (qmaExpandedPoint p).2 ≤ 6}

theorem qmaExpandedPoint_dist_row (p q : ℕ × ℕ) :
    Nat.dist (qmaExpandedPoint p).1 (qmaExpandedPoint q).1 = 32*Nat.dist p.1 q.1 := by
  simp only [qmaExpandedPoint,Nat.dist_add_add_right,Nat.dist_mul_left]

theorem qmaExpandedPoint_dist_col (p q : ℕ × ℕ) :
    Nat.dist (qmaExpandedPoint p).2 (qmaExpandedPoint q).2 = 32*Nat.dist p.2 q.2 := by
  simp only [qmaExpandedPoint,Nat.dist_add_add_right,Nat.dist_mul_left]

theorem qmaPatchBox_disjoint {p q : ℕ × ℕ} (hpq : p ≠ q) :
    Disjoint (qmaPatchBox p) (qmaPatchBox q) := by
  apply Set.disjoint_left.mpr
  intro z hz hq
  obtain ⟨hpx,hpy⟩ := hz
  obtain ⟨hqx,hqy⟩ := hq
  have hx := Nat.dist.triangle_inequality (qmaExpandedPoint p).1 z.1 (qmaExpandedPoint q).1
  have hy := Nat.dist.triangle_inequality (qmaExpandedPoint p).2 z.2 (qmaExpandedPoint q).2
  rw [Nat.dist_comm (qmaExpandedPoint p).1 z.1,qmaExpandedPoint_dist_row] at hx
  rw [Nat.dist_comm (qmaExpandedPoint p).2 z.2,qmaExpandedPoint_dist_col] at hy
  have heqx : Nat.dist p.1 q.1 = 0 := by omega
  have heqy : Nat.dist p.2 q.2 = 0 := by omega
  exact hpq (Prod.ext (Nat.eq_of_dist_eq_zero heqx) (Nat.eq_of_dist_eq_zero heqy))

theorem qmaExpandedPoint_mem_own (p : ℕ × ℕ) : qmaExpandedPoint p ∈ qmaPatchBox p := by
  simp [qmaPatchBox]

theorem qmaExpandedPoint_not_mem {p q : ℕ × ℕ} (hpq : p ≠ q) :
    qmaExpandedPoint p ∉ qmaPatchBox q := by
  intro h
  exact Set.disjoint_left.mp (qmaPatchBox_disjoint hpq) (qmaExpandedPoint_mem_own p) h

theorem qmaExpandedCrossing_not_vertex {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {x y : ℕ} {p : ℕ × ℕ} (hh : qmaHorizontalLane c y p) (hv : qmaVerticalLane d x p)
    (e : Fin C) (q : ℕ × ℕ) : qmaExpandedPoint (qmaLanePoint e q) ∉ qmaPatchBox p :=
  qmaExpandedPoint_not_mem (qmaLane_crossing_not_vertex hcd hh hv e q).symm

end ContinuumCoulomb

end OAI
