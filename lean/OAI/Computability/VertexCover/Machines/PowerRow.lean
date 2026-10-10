import Mathlib
import OAI.Computability.VertexCover.Machines.NatPath
import OAI.Computability.VertexCover.Machines.Generic

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

namespace VertexCover.Machine.PowerRowMachine
open UniqueGames.Foundations.PCP
open PoweringLabels PoweringEnumeration PoweringTables

abbrev Block (d n : ℕ) := Fin (2*d^(n+1))

def localRow {d : ℕ} (n : ℕ) (j : Block d n) (s : NatWalkMachine.State d) :
    GenericMachine.Row (labelCount d n) :=
  let w := (dartBlockEquiv d n).symm j
  ((if w.2 then (NatWalkMachine.word (n+1) w.1 s).2 else s.2,
    (2*d^(n+1))*s.2 + (dartBlockEquiv d n (w.1,!w.2)).val),
    GenericGraphTables.relationOf (fun a b =>
      if w.2 then NatPathMachine.path n w.1 ((paddedLabelEquiv d (n+1) 64).symm b)
        ((paddedLabelEquiv d (n+1) 64).symm a) s
      else NatPathMachine.path n w.1 ((paddedLabelEquiv d (n+1) 64).symm a)
        ((paddedLabelEquiv d (n+1) 64).symm b) s))

noncomputable def localTailPoly {d : ℕ} (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) natBits (fun s => (localRow n j s).1.1) := by
  let w := (dartBlockEquiv d n).symm j
  if h : w.2 then
    exact ((NatWalkMachine.wordPoly (n+1) w.1).comp
      (Poly.snd PortMachine.code natBits)).congr (fun _ => by simp [localRow,w,h])
  else
    exact (Poly.snd PortMachine.code natBits).congr (fun _ => by simp [localRow,w,h])
noncomputable def localReversePoly {d : ℕ} (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) natBits (fun s => (localRow n j s).1.2) := by
  let w := (dartBlockEquiv d n).symm j
  let v := Poly.snd (PortMachine.code (q := d)) natBits
  let c := Poly.const (NatWalkMachine.code (d := d)) natBits (2*d^(n+1))
  exact (((c.pair v).comp Poly.natMul).pair
    (Poly.const _ natBits (dartBlockEquiv d n (w.1,!w.2)).val)).comp Poly.natAdd
noncomputable def localRelationPoly {d : ℕ} (hd : 0<d) (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) GenericMachine.relationCode (fun s => (localRow n j s).2) := by
  let w := (dartBlockEquiv d n).symm j
  apply Poly.vectorOfFn
  intro i
  let a := (paddedLabelEquiv d (n+1) 64).symm ((GenericGraphTables.relationIndex (labelCount d n)).symm i).1
  let b := (paddedLabelEquiv d (n+1) 64).symm ((GenericGraphTables.relationIndex (labelCount d n)).symm i).2
  if h : w.2 then
    exact (NatPathMachine.pathPoly hd n w.1 b a).congr (fun _ => by simp [w,h,a,b])
  else
    exact (NatPathMachine.pathPoly hd n w.1 a b).congr (fun _ => by simp [w,h,a,b])
noncomputable def localPoly {d : ℕ} (hd : 0<d) (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) GenericMachine.rowCode (localRow n j) :=
  ((localTailPoly n j).pair (localReversePoly n j)).pair (localRelationPoly hd n j)
noncomputable def localVariablePoly {d : ℕ} (hd : 0<d) (n : ℕ) :
    Poly (prodBits (NatWalkMachine.code (d := d)) finCode) GenericMachine.rowCode
      (fun x => localRow n x.2 x.1) := by
  letI : Nonempty (Block d n) := ⟨⟨0,Nat.mul_pos (by decide) (Nat.pow_pos hd)⟩⟩
  exact Poly.finiteBranch NatWalkMachine.code finCode GenericMachine.rowCode (finCode_injective _)
    (fun s j => localRow n j s) (localPoly hd n)

def row {d : ℕ} (hd : 0<d) (n : ℕ) (x : PortTables.Input d × ℕ) : GenericMachine.Row (labelCount d n) :=
  localRow n ⟨x.2%(2*d^(n+1)),Nat.mod_lt _ (Nat.mul_pos (by decide) (Nat.pow_pos hd))⟩
    (x.1,x.2/(2*d^(n+1)))
noncomputable def rowPoly {d : ℕ} (hd : 0<d) (n : ℕ) :
    Poly (prodBits (PortMachine.code (q := d)) natBits) GenericMachine.rowCode (row hd n) := by
  let t := Poly.fst (PortMachine.code (q := d)) natBits
  let i := Poly.snd (PortMachine.code (q := d)) natBits
  let v := (i.pair (Poly.const _ natBits (2*d^(n+1)))).comp Poly.natDiv
  let j := i.comp (Poly.finMod (2*d^(n+1)) (Nat.mul_pos (by decide) (Nat.pow_pos hd)))
  exact ((t.pair v).pair j).comp (localVariablePoly hd n)

end VertexCover.Machine.PowerRowMachine
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
