import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanRoute

namespace OAI

/-! Exact support of the two-segment lattice route. -/

namespace ContinuumCoulomb

def qmaBetween (a b x : ℕ) : Prop := min a b ≤ x ∧ x ≤ max a b

def qmaManhattanSupport (p q z : ℕ × ℕ) : Prop :=
  (z.2 = p.2 ∧ qmaBetween p.1 q.1 z.1) ∨
    (z.1 = q.1 ∧ qmaBetween p.2 q.2 z.2)

theorem qmaAxisWalk_at_between {a b x : ℕ} (h : qmaBetween a b x) :
    qmaAxisWalk a b (Nat.dist a x) = x ∧ Nat.dist a x ≤ Nat.dist a b := by
  unfold qmaBetween qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

theorem qmaManhattanPoint_support (p q : ℕ × ℕ) (k : ℕ)
    (hk : k ≤ qmaManhattanLength p q) : qmaManhattanSupport p q (qmaManhattanPoint p q k) := by
  by_cases hx : k ≤ Nat.dist p.1 q.1
  · left
    simp only [qmaManhattanPoint,ite_eq_left hx]
    exact ⟨True.intro,qmaAxisWalk_bounds _ _ _ hx⟩
  · right
    have hy : k-Nat.dist p.1 q.1 ≤ Nat.dist p.2 q.2 := by
      unfold qmaManhattanLength at hk
      omega
    simp only [qmaManhattanPoint,ite_eq_right hx]
    exact ⟨True.intro,qmaAxisWalk_bounds _ _ _ hy⟩

theorem qmaManhattanSupport_point {p q z : ℕ × ℕ} (hz : qmaManhattanSupport p q z) :
    ∃ k, k ≤ qmaManhattanLength p q ∧ qmaManhattanPoint p q k = z := by
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩
  · obtain ⟨he,hk⟩ := qmaAxisWalk_at_between hx
    refine ⟨Nat.dist p.1 z.1,by unfold qmaManhattanLength; omega,?_⟩
    simp only [qmaManhattanPoint,ite_eq_left hk,he]
    exact Prod.ext rfl hy.symm
  · obtain ⟨he,hk⟩ := qmaAxisWalk_at_between hy
    refine ⟨Nat.dist p.1 q.1+Nat.dist p.2 z.2,by unfold qmaManhattanLength; omega,?_⟩
    by_cases hzero : Nat.dist p.2 z.2 = 0
    · have hyz := Nat.eq_of_dist_eq_zero hzero
      simp only [qmaManhattanPoint,hzero,add_zero,le_refl,ite_true,qmaAxisWalk_last]
      exact Prod.ext hx.symm hyz
    · have hn : ¬Nat.dist p.1 q.1+Nat.dist p.2 z.2 ≤ Nat.dist p.1 q.1 := by omega
      simp only [qmaManhattanPoint,ite_eq_right hn,Nat.add_sub_cancel_left,he]
      exact Prod.ext hx.symm rfl

theorem qmaManhattanRoute_range (p q z : ℕ × ℕ) :
    z ∈ Set.range (qmaManhattanRoute p q) ↔ qmaManhattanSupport p q z := by
  constructor
  · rintro ⟨k,rfl⟩
    exact qmaManhattanPoint_support p q k.val (by omega)
  · intro hz
    obtain ⟨k,hk,he⟩ := qmaManhattanSupport_point hz
    exact ⟨⟨k,by omega⟩,he⟩

end ContinuumCoulomb

end OAI
