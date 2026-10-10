import Mathlib
import OAI.Computability.VertexCover.Machines.Walk

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.NatWalkMachine
open UniqueGames.Foundations.PCP TableMachine

abbrev State (d : ℕ) := PortTables.Input d × ℕ
def code {d : ℕ} : State d → List Bool := prodBits PortMachine.code natBits

def step {d : ℕ} (p : Fin d) (s : State d) : State d :=
  (s.1,(ExpandMachine.lookup d (s.1.2.reverseIndex.toList.map Fin.val,s.2,p.val)).1)
noncomputable def stepPoly {d : ℕ} (p : Fin d) : Poly (code (d := d)) code (step p) := by
  let t := Poly.fst (PortMachine.code (q := d)) natBits
  let v := Poly.snd (PortMachine.code (q := d)) natBits
  let r := (((t.comp PortMachine.reverseListPoly).pair
    (v.pair (Poly.const code natBits p.val))).comp (ExpandMachine.lookupPoly d)).comp
      (Poly.fst natBits natBits)
  exact t.pair r

def word {d : ℕ} : (n : ℕ) → (Fin n → Fin d) → State d → State d
  | 0, _, s => s
  | n+1, p, s => word n (fun j => p j.succ) (step (p 0) s)
noncomputable def wordPoly {d : ℕ} : (n : ℕ) → (p : Fin n → Fin d) → Poly (code (d := d)) code (word n p)
  | 0, _ => Poly.identity code
  | n+1, p => (stepPoly (p 0)).comp (wordPoly n (fun j => p j.succ))

def edge {d : ℕ} : (n : ℕ) → (Fin (n+1) → Fin d) → Fin (n+1) → State d → State d × Fin d
  | 0, p, _, s => (s,p 0)
  | n+1, p, k, s => Fin.cases (s,p 0) (fun j => edge n (fun i => p i.succ) j (step (p 0) s)) k
noncomputable def edgePoly {d : ℕ} : (n : ℕ) → (p : Fin (n+1) → Fin d) → (k : Fin (n+1)) →
    Poly (code (d := d)) (prodBits code finCode) (edge n p k)
  | 0, p, _ => (Poly.identity code).pair (Poly.const code finCode (p 0))
  | n+1, p, k => Fin.cases
      ((Poly.identity code).pair (Poly.const code finCode (p 0)))
      (fun j => (stepPoly (p 0)).comp (edgePoly n (fun i => p i.succ) j)) k

noncomputable def stepVariablePoly {d : ℕ} (hd : 0<d) :
    Poly (prodBits (code (d := d)) finCode) code (fun x => step x.2 x.1) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact Poly.finiteBranch code finCode code (finCode_injective d) (fun s p => step p s) stepPoly

def forget {d : ℕ} (s : WalkMachine.State d) : State d := (s.1,s.2.val)
 theorem step_forget {d : ℕ} (p : Fin d) (s : WalkMachine.State d) :
    step p (forget s) = forget (WalkMachine.step p s) := by
  change (s.1,_)=(s.1,_)
  apply congrArg (fun n => (s.1,n))
  exact congrArg Prod.fst (OverlayMachine.lookup_port s.1.2 (s.2,p))
 theorem word_forget {d : ℕ} : ∀ (n : ℕ) (p : Fin n → Fin d) (s : WalkMachine.State d),
    word n p (forget s) = forget (WalkMachine.word n p s) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro p s; rw [word,step_forget,ih]; rfl
 theorem edge_forget {d : ℕ} : ∀ (n : ℕ) (p : Fin (n+1) → Fin d) (k : Fin (n+1)) (s : WalkMachine.State d),
    edge n p k (forget s) = (forget (WalkMachine.edge n p k s).1,(WalkMachine.edge n p k s).2) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro p k s
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp only [edge,Fin.cases_succ,step_forget,ih]
      rfl

def accepts {d : ℕ} (p : Fin d) (a b : GraphTables.Label) (s : State d) : Bool :=
  GraphTables.relationAt (s.1.2.relations.toList.getD (p.val+d*s.2) relationDefault) a b
noncomputable def acceptsPoly {d : ℕ} (p : Fin d) (a b : GraphTables.Label) :
    Poly (code (d := d)) boolBits (accepts p a b) := by
  let t := Poly.fst (PortMachine.code (q := d)) natBits
  let v := Poly.snd (PortMachine.code (q := d)) natBits
  let idx := ((Poly.const code natBits p.val).pair
    (((Poly.const code natBits d).pair v).comp Poly.natMul)).comp Poly.natAdd
  let r := (t.pair idx).comp PortMachine.relationPoly
  letI : Fintype GraphTables.RelationTable := Fintype.ofEquiv (Fin (64*64) → Bool)
    { toFun := Vector.ofFn
      invFun := fun r i => r[i]
      left_inv := by intro f; funext i; simp
      right_inv := by intro r; ext i; simp }
  exact r.comp (Poly.finite relationCode boolBits WalkMachine.relationCode_injective
    (fun t => GraphTables.relationAt t a b))
noncomputable def acceptsVariablePoly {d : ℕ} (hd : 0<d) :
    Poly (prodBits (code (d := d)) (prodBits finCode (prodBits finCode finCode))) boolBits
      (fun x => accepts x.2.1 x.2.2.1 x.2.2.2 x.1) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact Poly.finiteBranch code (prodBits finCode (prodBits finCode finCode)) boolBits
    (prodBits_injective (finCode_injective d)
      (prodBits_injective (finCode_injective 64) (finCode_injective 64)))
    (fun s x => accepts x.1 x.2.1 x.2.2 s) (fun x => acceptsPoly x.1 x.2.1 x.2.2)
 theorem accepts_forget {d : ℕ} (p : Fin d) (a b : GraphTables.Label) (s : WalkMachine.State d) :
    accepts p a b (forget s) = PortTables.accepts s.1.2 (s.2,p) a b := by
  unfold accepts forget
  rw [List.getD_eq_getElem _ _ (by simpa using (PortTables.rowIndex s.1.1 d (s.2,p)).isLt)]
  rfl

end VertexCover.Machine.NatWalkMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
