import Mathlib
import OAI.Computability.QuantumFactoring.Emits
import OAI.Computability.QuantumFactoring.CircuitFinalEmission
import OAI.Computability.QuantumFactoring.NetworkIndexedEmission

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma ite {c : α→Bool} {a b : α→β} (hc : Emits ea boolCode c)
    (ha : Emits ea eb a) (hb : Emits ea eb b) :
    Emits ea eb (fun x=>if c x then a x else b x):=by
  obtain ⟨pc⟩:=hc;obtain ⟨pa⟩:=ha;obtain ⟨pb⟩:=hb
  exact ofProcedure (Procedure.conditional pc pa pb)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {n m : β→ℕ}
lemma input {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits eb f)
    {g : α→β} (hg : Emits ea eb g) : NetEmits ea (fun x=>f (g x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ⟨fun x=>p (g x),hp.comp hg,fun x=>he (g x)⟩
end NetEmits
namespace PhysicalTreeEmission
open PhysicalTree
lemma zeroNet {α : Type} {ea : α→List Bool} {n : α→ℕ}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode (fun x=>quarterWidth (n x))) :
    NetEmits ea (fun x=>PhysicalTree.zeroNet (n x)):=by
  let p : α→ℕ→Pack:=fun x i=>if (1 ≤ i) ∧ (i < 1+n x) then constantPack (quarterWidth (n x)) true
    else bnotPack (bitPack (quarterWidth (n x)) i)
  have he:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hi:=he.fst.unaryNat
  have hN:=hn.comp he.snd
  have hW:=hw.comp he.snd
  have hc:=((hi.natLt (const _ _ 1)).boolNot).boolAnd
    (hi.natLt ((const _ _ 1).natAdd hN.unaryNat))
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=by
    have ha:=(ofProcedure Emission.constantPackP).comp (hW.pair (const _ _ true))
    have hb:=(ofProcedure Emission.bnotPackP).comp
      ((ofProcedure Emission.bitPackP).comp (hW.pair hi))
    exact (hc.ite ha hb).congr (by
      intro x
      simp only [p,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,not_lt,decide_eq_true_eq])
  apply NetEmits.allIndexed hw hw p hp
  intro x i
  simp only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and]
  dsimp only [p]
  split
  · exact constantPack_value _ _
  · exact bnotPack_value _ _ (bitPack_value i)
end PhysicalTreeEmission
end ExactQuantumFactoring.NetworkEmission

namespace ExactQuantumFactoring.UniformResources.PhysicalTree
open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission
open ExactQuantumFactoring.PhysicalTree
theorem uniform_of_quarter_emitters_clean
    (hw : Emits unaryCode unaryCode (fun l=>quarterWidth (paddedLength l)))
    (hp : OpsEmits unaryCode (fun l=>quarterProgram (paddedLength l)))
    (hf : NetEmits unaryCode (fun l=>quarterFlag (paddedLength l) (paddedLength_pos l)))
    (ho : NetEmits unaryCode (fun l=>quarterOutputNet (paddedLength l))) :
    Uniform finalCircuit:=by
  have hn : Emits unaryCode unaryCode paddedLength:=
    (const unaryCode unaryCode 128).unaryMax (BitStackProgram.Emits.id unaryCode)
  exact uniform_of_quarter_emitters hw hp hf (PhysicalTreeEmission.zeroNet hn hw) ho
end ExactQuantumFactoring.UniformResources.PhysicalTree

end



end OAI
