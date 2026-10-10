import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteCongestion

namespace OAI

/-! Distinct residue lanes separate parallel routes and keep crossings away from bends. -/

namespace ContinuumCoulomb

def qmaLanePoint {C : ℕ} (c : Fin C) (p : ℕ × ℕ) : ℕ × ℕ :=
  (C*p.1+c.val,C*p.2+c.val)

@[simp] theorem qmaLanePoint_row_mod {C : ℕ} (c : Fin C) (p : ℕ × ℕ) :
    (qmaLanePoint c p).1%C = c.val := by
  simp [qmaLanePoint,Nat.add_mod,Nat.mod_eq_of_lt c.isLt]

@[simp] theorem qmaLanePoint_col_mod {C : ℕ} (c : Fin C) (p : ℕ × ℕ) :
    (qmaLanePoint c p).2%C = c.val := by
  simp [qmaLanePoint,Nat.add_mod,Nat.mod_eq_of_lt c.isLt]

theorem qmaLanePoint_eq_color {C : ℕ} {c d : Fin C} {p q : ℕ × ℕ}
    (h : qmaLanePoint c p = qmaLanePoint d q) : c = d := by
  apply Fin.ext
  have he := congrArg (fun z : ℕ × ℕ => z.1%C) h
  simpa only [qmaLanePoint_row_mod] using he

theorem qmaLanePoint_injective {C : ℕ} (c : Fin C) : Function.Injective (qmaLanePoint c) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hC : 0 < C := (Nat.zero_le c.val).trans_lt c.isLt
  dsimp [qmaLanePoint] at hx hy
  apply Prod.ext
  · exact Nat.eq_of_mul_eq_mul_left hC (Nat.add_right_cancel hx)
  · exact Nat.eq_of_mul_eq_mul_left hC (Nat.add_right_cancel hy)

def qmaHorizontalLane {C : ℕ} (c : Fin C) (y : ℕ) (p : ℕ × ℕ) : Prop :=
  p.2 = C*y+c.val

def qmaVerticalLane {C : ℕ} (c : Fin C) (x : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 = C*x+c.val

theorem qmaHorizontalLane_color {C : ℕ} {c d : Fin C} {y z : ℕ} {p : ℕ × ℕ}
    (hc : qmaHorizontalLane c y p) (hd : qmaHorizontalLane d z p) : c = d := by
  apply Fin.ext
  have he : (C*y+c.val)%C = (C*z+d.val)%C := congrArg (fun x => x%C) (hc.symm.trans hd)
  simpa [Nat.add_mod,Nat.mod_eq_of_lt c.isLt,Nat.mod_eq_of_lt d.isLt] using he

theorem qmaVerticalLane_color {C : ℕ} {c d : Fin C} {x z : ℕ} {p : ℕ × ℕ}
    (hc : qmaVerticalLane c x p) (hd : qmaVerticalLane d z p) : c = d := by
  apply Fin.ext
  have he : (C*x+c.val)%C = (C*z+d.val)%C := congrArg (fun x => x%C) (hc.symm.trans hd)
  simpa [Nat.add_mod,Nat.mod_eq_of_lt c.isLt,Nat.mod_eq_of_lt d.isLt] using he

/-- A transverse crossing between distinct lanes cannot coincide with any lane vertex. -/
theorem qmaLane_crossing_not_vertex {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {x y : ℕ} {p : ℕ × ℕ} (hh : qmaHorizontalLane c y p) (hv : qmaVerticalLane d x p)
    (e : Fin C) (q : ℕ × ℕ) : p ≠ qmaLanePoint e q := by
  intro he
  subst p
  have hc : c = e := qmaHorizontalLane_color hh (by rfl : qmaHorizontalLane e q.2 (qmaLanePoint e q))
  have hd : d = e := qmaVerticalLane_color hv (by rfl : qmaVerticalLane e q.1 (qmaLanePoint e q))
  exact hcd (hc.trans hd.symm)

end ContinuumCoulomb

end OAI
