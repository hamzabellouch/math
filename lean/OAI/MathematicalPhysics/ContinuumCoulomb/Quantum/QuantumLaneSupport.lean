import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteLanes

namespace OAI

/-! Lane expansion preserves disjoint paths; different lanes meet only transversely. -/

namespace ContinuumCoulomb

def qmaLaneDown (C : ℕ) (z : ℕ × ℕ) : ℕ × ℕ := (z.1/C,z.2/C)

@[simp] theorem qmaLaneDown_point {C : ℕ} (c : Fin C) (p : ℕ × ℕ) :
    qmaLaneDown C (qmaLanePoint c p) = p := by
  have hC : 0 < C := (Nat.zero_le c.val).trans_lt c.isLt
  apply Prod.ext <;> dsimp [qmaLaneDown,qmaLanePoint]
  all_goals rw [Nat.add_comm,Nat.add_mul_div_left _ _ hC,Nat.div_eq_of_lt c.isLt,zero_add]

def qmaLaneSupport {C : ℕ} (c : Fin C) (p q z : ℕ × ℕ) : Prop :=
  qmaManhattanSupport (qmaLanePoint c p) (qmaLanePoint c q) z

theorem qmaLaneSupport_down {C : ℕ} (c : Fin C) {p q z : ℕ × ℕ}
    (hz : qmaLaneSupport c p q z) : qmaManhattanSupport p q (qmaLaneDown C z) := by
  have hdownp := qmaLaneDown_point c p
  have hdownq := qmaLaneDown_point c q
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩
  · left
    refine ⟨?_,?_⟩
    · have h := congrArg (fun x => x/C) hy
      change (qmaLaneDown C z).2 = (qmaLaneDown C (qmaLanePoint c p)).2 at h
      rw [hdownp] at h
      exact h
    · have h := qmaQuotient_bounds _ _ _ C hx.1 hx.2
      change min ((qmaLaneDown C (qmaLanePoint c p)).1) ((qmaLaneDown C (qmaLanePoint c q)).1) ≤
        (qmaLaneDown C z).1 ∧ (qmaLaneDown C z).1 ≤
        max ((qmaLaneDown C (qmaLanePoint c p)).1) ((qmaLaneDown C (qmaLanePoint c q)).1) at h
      simpa only [qmaBetween,hdownp,hdownq] using h
  · right
    refine ⟨?_,?_⟩
    · have h := congrArg (fun x => x/C) hx
      change (qmaLaneDown C z).1 = (qmaLaneDown C (qmaLanePoint c q)).1 at h
      rw [hdownq] at h
      exact h
    · have h := qmaQuotient_bounds _ _ _ C hy.1 hy.2
      change min ((qmaLaneDown C (qmaLanePoint c p)).2) ((qmaLaneDown C (qmaLanePoint c q)).2) ≤
        (qmaLaneDown C z).2 ∧ (qmaLaneDown C z).2 ≤
        max ((qmaLaneDown C (qmaLanePoint c p)).2) ((qmaLaneDown C (qmaLanePoint c q)).2) at h
      simpa only [qmaBetween,hdownp,hdownq] using h

theorem qmaLaneSupport_disjoint {C : ℕ} (c : Fin C) {p q u v : ℕ × ℕ}
    (h : Disjoint {z | qmaManhattanSupport p q z} {z | qmaManhattanSupport u v z}) :
    Disjoint {z | qmaLaneSupport c p q z} {z | qmaLaneSupport c u v z} := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact Set.disjoint_left.mp h (qmaLaneSupport_down c hz) (qmaLaneSupport_down c hz')

theorem qmaLaneSupport_transverse {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {p q u v z : ℕ × ℕ} (hc : qmaLaneSupport c p q z) (hd : qmaLaneSupport d u v z) :
    (qmaHorizontalLane c p.2 z ∧ qmaVerticalLane d v.1 z) ∨
      (qmaVerticalLane c q.1 z ∧ qmaHorizontalLane d u.2 z) := by
  rcases hc with ⟨hc,_⟩ | ⟨hc,_⟩ <;> rcases hd with ⟨hd,_⟩ | ⟨hd,_⟩
  · exact (hcd (qmaHorizontalLane_color hc hd)).elim
  · exact Or.inl ⟨hc,hd⟩
  · exact Or.inr ⟨hc,hd⟩
  · exact (hcd (qmaVerticalLane_color hc hd)).elim

theorem qmaLaneSupport_two_crossings {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {p q u v z : ℕ × ℕ} (hc : qmaLaneSupport c p q z) (hd : qmaLaneSupport d u v z) :
    z = (C*v.1+d.val,C*p.2+c.val) ∨ z = (C*q.1+c.val,C*u.2+d.val) := by
  rcases qmaLaneSupport_transverse hcd hc hd with ⟨hy,hx⟩ | ⟨hx,hy⟩
  · exact Or.inl (Prod.ext hx hy)
  · exact Or.inr (Prod.ext hx hy)

theorem qmaLaneSupport_crossing_not_vertex {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {p q u v z : ℕ × ℕ} (hc : qmaLaneSupport c p q z) (hd : qmaLaneSupport d u v z)
    (e : Fin C) (w : ℕ × ℕ) : z ≠ qmaLanePoint e w := by
  rcases qmaLaneSupport_transverse hcd hc hd with ⟨hh,hv⟩ | ⟨hv,hh⟩
  · exact qmaLane_crossing_not_vertex hcd hh hv e w
  · exact qmaLane_crossing_not_vertex hcd.symm hh hv e w

end ContinuumCoulomb

end OAI
