import Mathlib
import OAI.Computability.VertexCover.Machines.FinCode
import OAI.Computability.VertexCover.Machines.Codec
import OAI.Computability.VertexCover.Machines.Overlay
import OAI.Computability.VertexCover.Machines.FixedOps

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

namespace VertexCover.Machine.WalkMachine
open UniqueGames.Foundations.PCP
open PoweringWalks TableMachine

abbrev State (d : ℕ) := Σ T : PortTables.Input d, Fin T.1
def code {d : ℕ} (s : State d) : List Bool := prodBits PortMachine.code natBits (s.1,s.2.val)
def step {d : ℕ} (p : Fin d) (s : State d) : State d :=
  ⟨s.1,next (PortTables.portGraph s.1.2) s.2 p⟩

noncomputable def tablePoly {d : ℕ} : Poly (code (d := d)) PortMachine.code Sigma.fst :=
  (Poly.fst PortMachine.code natBits).encodeCongr (fun s => (s.1,s.2.val)) (fun _ => rfl) (fun _ => rfl)
noncomputable def vertexPoly {d : ℕ} : Poly (code (d := d)) natBits (fun s => s.2.val) :=
  (Poly.snd PortMachine.code natBits).encodeCongr (fun s => (s.1,s.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def stepPoly {d : ℕ} (p : Fin d) : Poly (code (d := d)) code (step p) := by
  let rs := (tablePoly (d := d)).comp PortMachine.reverseListPoly
  let x := vertexPoly.pair (Poly.const (code (d := d)) natBits p.val)
  let r := ((rs.pair x).comp (ExpandMachine.lookupPoly d)).comp (Poly.fst natBits natBits)
  exact (tablePoly.pair r).encodeCongr id (fun _ => rfl) (fun s => by
    change prodBits PortMachine.code natBits (s.1,_) = prodBits PortMachine.code natBits (s.1,_)
    apply congrArg (fun n => prodBits PortMachine.code natBits (s.1,n))
    exact congrArg Prod.fst (OverlayMachine.lookup_port s.1.2 (s.2,p)))

def word {d : ℕ} (n : ℕ) (p : Fin n → Fin d) (s : State d) : State d :=
  ⟨s.1,wordEnd (PortTables.portGraph s.1.2) n s.2 p⟩
noncomputable def wordPoly {d : ℕ} : (n : ℕ) → (p : Fin n → Fin d) → Poly (code (d := d)) code (word n p)
  | 0, _ => Poly.identity code
  | n+1, p => (stepPoly (p 0)).comp (wordPoly n (fun j => p j.succ))

def edge {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d) (k : Fin (n+1)) (s : State d) : State d × Fin d :=
  let e := edgeAt (PortTables.portGraph s.1.2) n (s.2,p) k
  (⟨s.1,e.1⟩,e.2)
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

 theorem relationCode_injective : Function.Injective relationCode := by
  intro a b hab
  exact Vector.toList_inj.mp hab

noncomputable def acceptsPoly {d : ℕ} (p : Fin d) (a b : GraphTables.Label) :
    Poly (code (d := d)) boolBits (fun s => PortTables.accepts s.1.2 (s.2,p) a b) := by
  let v := vertexPoly (d := d)
  let idx := ((Poly.const code natBits p.val).pair
    (((Poly.const code natBits d).pair v).comp Poly.natMul)).comp Poly.natAdd
  let r := (tablePoly.pair idx).comp PortMachine.relationPoly
  letI : Fintype GraphTables.RelationTable := Fintype.ofEquiv (Fin (64*64) → Bool)
    { toFun := Vector.ofFn
      invFun := fun r i => r[i]
      left_inv := by intro f; funext i; simp
      right_inv := by intro r; ext i; simp }
  let result := r.comp (Poly.finite relationCode boolBits relationCode_injective
    (fun t => GraphTables.relationAt t a b))
  exact result.congr (fun s => by
    change GraphTables.relationAt (s.1.2.relations.toList.getD (p.val+d*s.2.val) relationDefault) a b = _
    rw [List.getD_eq_getElem _ _ (by simpa using (PortTables.rowIndex s.1.1 d (s.2,p)).isLt)]
    rfl)

noncomputable def acceptsVariablePoly {d : ℕ} (hd : 0<d) :
    Poly (prodBits (code (d := d)) (prodBits finCode (prodBits finCode finCode))) boolBits
      (fun x => PortTables.accepts x.1.1.2 (x.1.2,x.2.1) x.2.2.1 x.2.2.2) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact Poly.finiteBranch code (prodBits finCode (prodBits finCode finCode)) boolBits
    (prodBits_injective (finCode_injective d)
      (prodBits_injective (finCode_injective 64) (finCode_injective 64)))
    (fun s x => PortTables.accepts s.1.2 (s.2,x.1) x.2.1 x.2.2)
    (fun x => acceptsPoly x.1 x.2.1 x.2.2)

end VertexCover.Machine.WalkMachine
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
