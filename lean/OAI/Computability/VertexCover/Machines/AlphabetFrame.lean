import Mathlib
import OAI.Computability.VertexCover.Machines.ListFilter
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

namespace VertexCover.Machine.AlphabetMachine
open UniqueGames.Foundations.PCP
open AlphabetTable
open Enumeration

@[instance_reducible] noncomputable def relationFintype (q : ℕ) : Fintype (GenericGraphTables.RelationTable q) :=
  Fintype.ofEquiv (Fin (q*q) → Bool)
    {toFun := Vector.ofFn, invFun := fun r i => r[i]
     left_inv := by intro f; funext i; simp
     right_inv := by intro r; ext i; simp}
 theorem relationCode_injective (q : ℕ) : Function.Injective (GenericMachine.relationCode (q := q)) :=
  fun _ _ h => Vector.toList_inj.mp h

abbrev State (q : ℕ) := GenericGraphTables.Table q × ℕ
def code {q : ℕ} : State q → List Bool := prodBits GenericMachine.code natBits
def old {q : ℕ} (s : State q) : GenericMachine.Row q := (GenericMachine.erase s.1).2.getD s.2 (GenericMachine.rowDefault q)
def head {q : ℕ} (s : State q) : ℕ :=
  ((GenericMachine.erase s.1).2.getD (old s).1.2 (GenericMachine.rowDefault q)).1.1
noncomputable def tablePoly {q : ℕ} : Poly (code (q := q)) GenericMachine.code Prod.fst := Poly.fst _ _
noncomputable def indexPoly {q : ℕ} : Poly (code (q := q)) natBits Prod.snd := Poly.snd _ _
noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => s.1.vertices) :=
  tablePoly.comp GenericMachine.verticesPoly
noncomputable def dartsPoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => s.1.darts) :=
  tablePoly.comp GenericMachine.dartsPoly
noncomputable def oldPoly {q : ℕ} : Poly (code (q := q)) GenericMachine.rowCode old := GenericMachine.lookupPoly
noncomputable def tailPoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => (old s).1.1) :=
  oldPoly.comp ((Poly.fst (prodBits natBits natBits) GenericMachine.relationCode).comp (Poly.fst natBits natBits))
noncomputable def reversePoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => (old s).1.2) :=
  oldPoly.comp ((Poly.fst (prodBits natBits natBits) GenericMachine.relationCode).comp (Poly.snd natBits natBits))
noncomputable def relationPoly {q : ℕ} : Poly (code (q := q)) GenericMachine.relationCode (fun s => (old s).2) :=
  oldPoly.comp (Poly.snd (prodBits natBits natBits) GenericMachine.relationCode)
noncomputable def headPoly {q : ℕ} : Poly (code (q := q)) natBits head :=
  ((tablePoly.pair reversePoly).comp GenericMachine.lookupPoly).comp
    ((Poly.fst (prodBits natBits natBits) GenericMachine.relationCode).comp (Poly.fst natBits natBits))
noncomputable def loopPoly {q : ℕ} : Poly (code (q := q)) boolBits (fun s => decide ((old s).1.1=head s)) :=
  (tailPoly.pair headPoly).comp Poly.natEq

abbrev Local (q : ℕ) := (AlphabetGraph.LocalEvent (Fin q) × Fin 6) × Bool
def blockCount (q : ℕ) : ℕ := localCount q * 12
def blockEquiv (q : ℕ) : Local q ≃ Fin (blockCount q) :=
  (productEquiv (productEquiv (localEventEquiv q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [blockCount,Nat.mul_assoc]))
 theorem block_pos (q : ℕ) : 0<blockCount q := by
  unfold blockCount localCount fiveTapeCount pairTapeCount tapeCount
  positivity
 theorem block_val (q : ℕ) (l : Local q) :
    (blockEquiv q l).val = (localEventEquiv q l.1.1).val*12 + l.1.2.val*2+bitValue l.2 := by
  change (boolEquiv l.2).val+2*(l.1.2.val+6*(localEventEquiv q l.1.1).val)=_
  rw [boolEquiv_val]
  omega
 theorem dart_block_val {q m : ℕ} (e : Fin m) (l : Local q) :
    (dartEquiv m q (((e,l.1.1),l.1.2),l.2)).val = (blockEquiv q l).val+blockCount q*e.val := by
  rw [dartEquiv_val,eventEquiv_val,block_val]
  unfold blockCount
  ring

end VertexCover.Machine.AlphabetMachine
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
