import Mathlib
import OAI.Computability.QuantumFactoring.FactoringCircuit
import OAI.Computability.QuantumFactoring.CircuitProgramEmission

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α : Type} {ea : α→List Bool}
lemma unaryMax {f g : α→ℕ} (hf : Emits ea unaryCode f) (hg : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>max (f x) (g x)):=by
  exact ((ofProcedure clippedUnary).comp ((hf.unaryAdd hg).pair
    (hf.unaryNat.natMax hg.unaryNat))).congr (by intro x;exact min_eq_right (max_le (by omega) (by omega)))
lemma range {f : α→ℕ} (hf : Emits ea unaryCode f) : Emits ea (listCode Nat.bits) (fun x=>List.range (f x)):=
  (ofProcedure NetworkEmission.Emission.rangeP).comp hf
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q r : α→ℕ}
lemma place {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (w : ∀x,Register (q x) (r x)) (f : α→ℕ→ℕ)
    (hw : ∀x i,(w x i).val=f x i.val)
    (hf : Emits (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    OpsEmits ea (fun x=>(p x).map (Instruction.place (w x))):=by
  obtain ⟨pf⟩:=hf
  exact ((ofProcedure (Emission.opsMapWith pf)).comp ((BitStackProgram.Emits.id ea).pair hp)).congr (by
    intro x
    simp only [List.map_map]
    apply List.map_congr_left
    intro o ho
    exact (eraseOp_place (w x) o (f x) (hw x)).symm)
end OpsEmits
namespace Emission
noncomputable def relocateValP : Procedure
    (prodCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits) Nat.bits
    (fun x=>relocateVal x.1.1 x.1.2.1 x.1.2.2 x.2):=by
  let e:=first (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let i:=second (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let a:=(first Nat.bits (prodCode Nat.bits Nat.bits)).comp e
  let m:=(first Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let l:=(second Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let z:=binaryEq.comp (i.pair (constant _ Nat.bits 0))
  let il:=boolNot.comp (binaryLt.comp (l.pair i))
  let ia:=binaryLt.comp (i.pair a)
  let iam:=binaryLt.comp (i.pair (binaryAdd.comp (a.pair m)))
  let case0:=binaryAdd.comp (l.pair m)
  let case1:=binarySub.comp (i.pair (constant _ Nat.bits 1))
  let case2:=binaryAdd.comp (i.pair m)
  let case3:=binaryAdd.comp (l.pair (binarySub.comp (i.pair a)))
  exact (conditional z case0 (conditional il case1 (conditional ia case2 (conditional iam case3 i)))).congrFun (by
    intro x;simp only [Function.comp_apply,decide_eq_true_eq,relocateVal,Bool.not_eq_true',decide_eq_false_iff_not,not_lt])
end Emission
end ExactQuantumFactoring.CircuitEmission

namespace ExactQuantumFactoring.UniformResources.PhysicalTree
open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission
open ExactQuantumFactoring.PhysicalTree

/-- A precise remaining syntax boundary. All post-quarter amplification,
clean oracle synthesis, readout, relocation, and unary serialization are actual
charged finite-stack procedures; none is a generation-time oracle. -/
theorem uniform_of_quarter_emitters
    (hw : Emits unaryCode unaryCode (fun l=>quarterWidth (paddedLength l)))
    (hp : OpsEmits unaryCode (fun l=>quarterProgram (paddedLength l)))
    (hf : NetEmits unaryCode (fun l=>quarterFlag (paddedLength l) (paddedLength_pos l)))
    (hz : NetEmits unaryCode (fun l=>zeroNet (paddedLength l)))
    (ho : NetEmits unaryCode (fun l=>quarterOutputNet (paddedLength l))) :
    Uniform finalCircuit:=by
  have hr : Emits unaryCode unaryCode (fun l=>reflectWork (paddedLength l) (paddedLength_pos l)):=hf.count.unaryMax hz.count
  have ha : Emits unaryCode unaryCode (fun l=>amplifiedWidth (paddedLength l) (paddedLength_pos l)):=hw.unarySucc.unaryAdd hr
  have hs : NetEmits unaryCode (fun l=>BooleanNetwork.select
      (firstRegister (quarterWidth (paddedLength l)) 1 (reflectWork (paddedLength l) (paddedLength_pos l)))):=by
    apply NetEmits.select ha
    exact hw.range.congr (by intro l;change List.range (quarterWidth (paddedLength l))=List.ofFn (fun i:Fin (quarterWidth (paddedLength l))=>i.val);exact (ofFn_val_range _).symm)
  have hao : NetEmits unaryCode (fun l=>amplifiedOutput (paddedLength l) (paddedLength_pos l)):=hs.comp ho
  have hap : OpsEmits unaryCode (fun l=>amplifiedProgram (paddedLength l) (paddedLength_pos l)):=
    hp.amplify hf hz (fun _=>Nat.le_max_left _ _) (fun _=>Nat.le_max_right _ _)
  have hfact : OpsEmits unaryCode (fun l=>factoringProgram (paddedLength l) (paddedLength_pos l)):=
    hap.readout hao (fun _=>le_rfl)
  have hn : Emits unaryCode unaryCode paddedLength:=
    (const unaryCode unaryCode 128).unaryMax (BitStackProgram.Emits.id unaryCode)
  have hm:=hn.unaryMul hn
  have hq : Emits unaryCode unaryCode (fun l=>readoutWidth (paddedLength l) (paddedLength_pos l)):=
    (ha.unaryAdd hm).unaryAdd hao.count
  have hrel : Emits (prodCode unaryCode Nat.bits) Nat.bits
      (fun x=>relocateVal (amplifiedWidth (paddedLength x.1) (paddedLength_pos x.1))
        (paddedLength x.1*paddedLength x.1) x.1 x.2):=by
    have he:=(BitStackProgram.Emits.id (prodCode unaryCode Nat.bits)).fst
    have hi:=(BitStackProgram.Emits.id (prodCode unaryCode Nat.bits)).snd
    exact (ofProcedure CircuitEmission.Emission.relocateValP).comp
      (((ha.unaryNat.comp he).pair ((hm.unaryNat.comp he).pair he.unaryNat)).pair hi)
  have hP : OpsEmits unaryCode (fun l=>(finalCircuit l).instructions):=
    hfact.place finalRegister
      (fun l i=>relocateVal (amplifiedWidth (paddedLength l) (paddedLength_pos l))
        (paddedLength l*paddedLength l) l i) (fun _ _=>rfl) hrel
  obtain ⟨pp⟩:=(ofProcedure CircuitEmission.Emission.dataPackP).comp (hq.pair hP)
  exact CircuitEmission.uniform_of_emitter finalCircuit pp
end ExactQuantumFactoring.UniformResources.PhysicalTree

end



end OAI
