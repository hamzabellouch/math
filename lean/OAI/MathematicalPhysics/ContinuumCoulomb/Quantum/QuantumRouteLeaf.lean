import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridWalk

namespace OAI

/-! Reserve one singlet leaf beside the initial step of every scaled route.
Four incident directions use four different quadrants. -/

namespace ContinuumCoulomb

def qmaLeafCenter (p : ℕ × ℕ) : ℕ × ℕ := (8*p.1+4,8*p.2+4)

def qmaLeafFirst (p : ℕ × ℕ) : Fin 4 → ℕ × ℕ :=
  ![(8*p.1+5,8*p.2+4),(8*p.1+4,8*p.2+5),
    (8*p.1+3,8*p.2+4),(8*p.1+4,8*p.2+3)]

def qmaRouteLeaf (p : ℕ × ℕ) : Fin 4 → ℕ × ℕ :=
  ![(8*p.1+5,8*p.2+5),(8*p.1+3,8*p.2+5),
    (8*p.1+3,8*p.2+3),(8*p.1+5,8*p.2+3)]

theorem qmaLeafFirst_step (p : ℕ × ℕ) (a : Fin 4) :
    qmaSquareGrid.Adj (qmaLeafCenter p) (qmaLeafFirst p a) := by
  fin_cases a <;> simp [qmaSquareGrid,qmaLeafCenter,qmaLeafFirst,Nat.dist]

theorem qmaRouteLeaf_step (p : ℕ × ℕ) (a : Fin 4) :
    qmaSquareGrid.Adj (qmaLeafFirst p a) (qmaRouteLeaf p a) := by
  fin_cases a <;> simp [qmaSquareGrid,qmaLeafFirst,qmaRouteLeaf,Nat.dist]

theorem qmaRouteLeaf_cell (p : ℕ × ℕ) (a : Fin 4) :
    ((qmaRouteLeaf p a).1/8,(qmaRouteLeaf p a).2/8) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaRouteLeaf,Nat.add_div]

theorem qmaRouteLeaf_not_gridline (p : ℕ × ℕ) (a : Fin 4) :
    (qmaRouteLeaf p a).1%8 ≠ 4 ∧ (qmaRouteLeaf p a).2%8 ≠ 4 := by
  fin_cases a <;> norm_num [qmaRouteLeaf,Nat.add_mod]

theorem qmaRouteLeaf_avoids (p z : ℕ × ℕ) (a : Fin 4)
    (hz : z.1%8 = 4 ∨ z.2%8 = 4) : qmaRouteLeaf p a ≠ z := by
  intro he
  obtain ⟨hx,hy⟩ := qmaRouteLeaf_not_gridline p a
  rw [he] at hx hy
  exact hz.elim hx hy

theorem qmaRouteLeaf_injective : Function.Injective
    (fun x : (ℕ × ℕ) × Fin 4 => qmaRouteLeaf x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have hpq : p = q := by
    have he := congrArg (fun z : ℕ × ℕ => (z.1/8,z.2/8)) h
    simpa only [qmaRouteLeaf_cell] using he
  subst q
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hab : a = b := by
    fin_cases a <;> fin_cases b <;> simp [qmaRouteLeaf] at hx hy ⊢
  subst b
  rfl

theorem qmaRouteLeaf_bounds {X Y : ℕ} {p : ℕ × ℕ} (hx : p.1 < X) (hy : p.2 < Y)
    (a : Fin 4) : (qmaRouteLeaf p a).1 < 8*X ∧ (qmaRouteLeaf p a).2 < 8*Y := by
  fin_cases a <;> simp [qmaRouteLeaf] <;> omega

end ContinuumCoulomb

end OAI
