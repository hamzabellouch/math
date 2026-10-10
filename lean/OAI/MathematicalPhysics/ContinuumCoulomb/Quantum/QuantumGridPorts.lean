import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTranslatedPatch
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighborsFour

namespace OAI

/-! Distinct entry and exit spin locations for every grid cell. -/

namespace ContinuumCoulomb

def qmaGridPort (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  ![(32*p.1+23,32*p.2+16),(32*p.1+16,32*p.2+23),
    (32*p.1+9,32*p.2+16),(32*p.1+16,32*p.2+9)] a

theorem qmaGridPort_cell (p : ℕ × ℕ) (a : Fin 4) :
    ((qmaGridPort p a).1/32,(qmaGridPort p a).2/32) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaGridPort,Nat.add_div]

theorem qmaGridPort_injective : Function.Injective (fun x : (ℕ × ℕ) × Fin 4 => qmaGridPort x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  simp only [qmaGridPort_cell] at he
  subst q
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hab : a = b := by
    fin_cases a <;> fin_cases b <;> simp [qmaGridPort] at hx hy ⊢
  subst b
  rfl

theorem qmaGridPort_ne_center (p q : ℕ × ℕ) (a : Fin 4) : qmaGridPort p a ≠ qmaExpandedPoint q := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> simp [qmaGridPort,qmaExpandedPoint] at hx hy <;> omega

theorem qmaExpandedPoint_injective : Function.Injective qmaExpandedPoint := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp only [qmaExpandedPoint] at hx hy <;> omega

def qmaDirectedPort (p q : ℕ × ℕ) : ℕ × ℕ := qmaGridPort p (qmaGridNeighborIndex p q)

theorem qmaDirectedPort_injective {p q r s : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (hr : 0 < r.1 ∧ 0 < r.2)
    (hpq : qmaSquareGrid.Adj p q) (hrs : qmaSquareGrid.Adj r s)
    (h : qmaDirectedPort p q = qmaDirectedPort r s) : p = r ∧ q = s := by
  have he : (p,qmaGridNeighborIndex p q) = (r,qmaGridNeighborIndex r s) := qmaGridPort_injective h
  constructor
  · exact congrArg Prod.fst he
  · have hh := congrArg (fun z : (ℕ × ℕ) × Fin 4 => qmaGridNeighbor z.1 z.2) he
    simpa only [qmaGridNeighborIndex_spec hp.1 hp.2 hpq,qmaGridNeighborIndex_spec hr.1 hr.2 hrs] using hh

theorem qmaGridPort_bounds {p : ℕ × ℕ} {X Y : ℕ} (hx : p.1 < X) (hy : p.2 < Y) (a : Fin 4) :
    (qmaGridPort p a).1 < 32*X ∧ (qmaGridPort p a).2 < 32*Y := by
  fin_cases a <;> simp [qmaGridPort] <;> omega

end ContinuumCoulomb

end OAI
