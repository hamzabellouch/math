import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumScaledEdge

namespace OAI

/-! Interior points of two scaled unit segments can coincide only when the
underlying grid edge is the same, possibly with reversed orientation. -/

namespace ContinuumCoulomb

def qmaScaledDirectionPoint (p : ℕ × ℕ) (a : Fin 4) (k : ℕ) : ℕ × ℕ :=
  ![(8*p.1+4+k,8*p.2+4),(8*p.1+4,8*p.2+4+k),
    (8*p.1+4-k,8*p.2+4),(8*p.1+4,8*p.2+4-k)] a

theorem qmaScaledDirectionPoint_eq (p : ℕ × ℕ) (hx : 0 < p.1) (hy : 0 < p.2)
    (a : Fin 4) {k : ℕ} (hk : k ≤ 8) :
    qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter (qmaGridNeighbor p a)) k =
      qmaScaledDirectionPoint p a k := by
  have hpx : p.1-1+1 = p.1 := by omega
  have hpy : p.2-1+1 = p.2 := by omega
  fin_cases a <;> simp [qmaManhattanPoint,qmaAxisWalk,qmaLeafCenter,qmaGridNeighbor,
    qmaScaledDirectionPoint,Nat.dist]
  all_goals first | omega | (split_ifs <;> simp only [Prod.mk.injEq] <;> omega)

theorem qmaScaledDirectionPoint_not_center (p r : ℕ × ℕ)
    (a : Fin 4) {k : ℕ} (hk : 0 < k) (hk8 : k < 8) :
    qmaScaledDirectionPoint p a k ≠ qmaLeafCenter r := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  fin_cases a <;> simp [qmaScaledDirectionPoint,qmaLeafCenter] at h1 h2 <;> omega

theorem qmaScaledDirectionPoint_collision (p r : ℕ × ℕ)
    (hpx : 0 < p.1) (hpy : 0 < p.2) (hrx : 0 < r.1) (hry : 0 < r.2)
    (a b : Fin 4) {i j : ℕ} (hi : 0 < i) (hi8 : i < 8) (hj : 0 < j) (hj8 : j < 8)
    (h : qmaScaledDirectionPoint p a i = qmaScaledDirectionPoint r b j) :
    (p = r ∧ qmaGridNeighbor p a = qmaGridNeighbor r b) ∨
      (p = qmaGridNeighbor r b ∧ qmaGridNeighbor p a = r) := by
  rcases p with ⟨x,y⟩
  rcases r with ⟨u,v⟩
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  fin_cases a <;> fin_cases b <;>
    simp [qmaScaledDirectionPoint,qmaGridNeighbor,Prod.mk.injEq] at h1 h2 ⊢ <;> omega

theorem qmaScaledEdge_inner_collision {p q r s : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (hr : 0 < r.1 ∧ 0 < r.2)
    (hpq : qmaSquareGrid.Adj p q) (hrs : qmaSquareGrid.Adj r s)
    {i j : ℕ} (hi : 0 < i) (hi8 : i < 8) (hj : 0 < j) (hj8 : j < 8)
    (h : qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) i =
      qmaManhattanPoint (qmaLeafCenter r) (qmaLeafCenter s) j) :
    (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  obtain ⟨a,rfl⟩ := qmaGridNeighbor_exists hpq
  obtain ⟨b,rfl⟩ := qmaGridNeighbor_exists hrs
  rw [qmaScaledDirectionPoint_eq p hp.1 hp.2 a hi8.le,
    qmaScaledDirectionPoint_eq r hr.1 hr.2 b hj8.le] at h
  exact qmaScaledDirectionPoint_collision p r hp.1 hp.2 hr.1 hr.2 a b hi hi8 hj hj8 h

end ContinuumCoulomb

end OAI
