import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridPorts

namespace OAI

/-! Moving crossing terminals one unit into their private patch leaves the
external corridors free and creates space for the two mediator spins. -/

namespace ContinuumCoulomb

def qmaInnerPort (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  ![(32*p.1+22,32*p.2+16),(32*p.1+16,32*p.2+22),
    (32*p.1+10,32*p.2+16),(32*p.1+16,32*p.2+10)] a

def qmaGadgetAncilla (p : ℕ × ℕ) (b : Fin 2) : ℕ × ℕ :=
  ![(32*p.1+14,32*p.2+18),(32*p.1+18,32*p.2+14)] b

theorem qmaInnerPort_cell (p : ℕ × ℕ) (a : Fin 4) :
    ((qmaInnerPort p a).1/32,(qmaInnerPort p a).2/32) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaInnerPort,Nat.add_div]

theorem qmaGadgetAncilla_cell (p : ℕ × ℕ) (a : Fin 2) :
    ((qmaGadgetAncilla p a).1/32,(qmaGadgetAncilla p a).2/32) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaGadgetAncilla,Nat.add_div]

theorem qmaExpandedPoint_cell (p : ℕ × ℕ) :
    ((qmaExpandedPoint p).1/32,(qmaExpandedPoint p).2/32) = p := by
  apply Prod.ext <;> simp [qmaExpandedPoint,Nat.add_div]

theorem qmaInnerPort_injective : Function.Injective
    (fun x : (ℕ × ℕ) × Fin 4 => qmaInnerPort x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  simp only [qmaInnerPort_cell] at he
  subst q
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hab : a = b := by fin_cases a <;> fin_cases b <;> simp [qmaInnerPort] at hx hy ⊢
  subst b
  rfl

theorem qmaGadgetAncilla_injective : Function.Injective
    (fun x : (ℕ × ℕ) × Fin 2 => qmaGadgetAncilla x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  simp only [qmaGadgetAncilla_cell] at he
  subst q
  have hx := congrArg Prod.fst h
  have hab : a = b := by fin_cases a <;> fin_cases b <;> simp [qmaGadgetAncilla] at hx ⊢
  subst b
  rfl

theorem qmaInnerPort_ne_center (p q : ℕ × ℕ) (a : Fin 4) :
    qmaInnerPort p a ≠ qmaExpandedPoint q := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> simp [qmaInnerPort,qmaExpandedPoint] at hx hy <;> omega

theorem qmaInnerPort_ne_port (p q : ℕ × ℕ) (a b : Fin 4) :
    qmaInnerPort p a ≠ qmaGridPort q b := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> fin_cases b <;> simp [qmaInnerPort,qmaGridPort] at hx hy <;> omega

theorem qmaGadgetAncilla_ne_center (p q : ℕ × ℕ) (a : Fin 2) :
    qmaGadgetAncilla p a ≠ qmaExpandedPoint q := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases a <;> simp [qmaGadgetAncilla,qmaExpandedPoint] at hx <;> omega

theorem qmaGadgetAncilla_ne_port (p q : ℕ × ℕ) (a : Fin 2) (b : Fin 4) :
    qmaGadgetAncilla p a ≠ qmaGridPort q b := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases a <;> fin_cases b <;> simp [qmaGadgetAncilla,qmaGridPort] at hx <;> omega

theorem qmaGadgetAncilla_ne_inner (p q : ℕ × ℕ) (a : Fin 2) (b : Fin 4) :
    qmaGadgetAncilla p a ≠ qmaInnerPort q b := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases a <;> fin_cases b <;> simp [qmaGadgetAncilla,qmaInnerPort] at hx <;> omega

def qmaPortIndex (z : ℕ × ℕ) : Fin 4 :=
  if z.1%32 = 23 then 0 else if z.2%32 = 23 then 1 else if z.1%32 = 9 then 2 else 3

theorem qmaPortIndex_spec (p : ℕ × ℕ) (a : Fin 4) : qmaPortIndex (qmaGridPort p a) = a := by
  fin_cases a <;> simp [qmaPortIndex,qmaGridPort,Nat.add_mod]

def qmaCrossingMove (cross : (ℕ × ℕ) → Prop) [DecidablePred cross] (z : ℕ × ℕ) : ℕ × ℕ :=
  let p := (z.1/32,z.2/32)
  if cross p ∧ z ≠ qmaExpandedPoint p then qmaInnerPort p (qmaPortIndex z) else z

theorem qmaCrossingMove_center (cross : (ℕ × ℕ) → Prop) [DecidablePred cross] (p : ℕ × ℕ) :
    qmaCrossingMove cross (qmaExpandedPoint p) = qmaExpandedPoint p := by
  simp [qmaCrossingMove,qmaExpandedPoint_cell]

theorem qmaCrossingMove_port (cross : (ℕ × ℕ) → Prop) [DecidablePred cross] (p : ℕ × ℕ) (a : Fin 4) :
    qmaCrossingMove cross (qmaGridPort p a) = if cross p then qmaInnerPort p a else qmaGridPort p a := by
  simp only [qmaCrossingMove,qmaGridPort_cell,qmaPortIndex_spec]
  by_cases hp : cross p
  · rw [ite_eq_left ⟨hp,qmaGridPort_ne_center p p a⟩,ite_eq_left hp]
  · rw [ite_eq_right (fun h => hp h.1),ite_eq_right hp]

end ContinuumCoulomb

end OAI
