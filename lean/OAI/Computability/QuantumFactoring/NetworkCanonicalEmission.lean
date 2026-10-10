import Mathlib
import OAI.Computability.QuantumFactoring.NetworkAt
import OAI.Computability.QuantumFactoring.WordBlocksEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
noncomputable def massP : Procedure dataCode Nat.bits Data.mass:=
  binaryAdd.comp (dataWidthP.pair ((listLength Nat.bits 0).comp dataOutputsP))
def canonicalPack (p : Pack) : Pack:=⟨⟨p.val.value.mass,p.val.value⟩,p.property.1,le_rfl⟩
noncomputable def canonicalPackP : Procedure packCode packCode canonicalPack:=by
  let hv:=packValueP
  let hmass:=boundedUnary (massP.comp hv) packBudgetP (fun x=>x.property.2)
  exact (hmass.pair hv).result (by intro x;rfl)
lemma canonicalPack_erase {n m : ℕ} (p : Pack) (a : BooleanNetwork n m)
    (h : p.val.value=erase a) : canonicalPack p=erasePack a:=by
  apply Subtype.ext
  change PackData.mk _ _=PackData.mk _ _
  congr 1
  · rw [h]
    simp only [Data.mass,Data.width,erase,eraseNet_length,List.length_ofFn]
end Emission
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m : α→ℕ} {f : ∀x,BooleanNetwork (n x) (m x)}
lemma canonical (hf : NetEmits ea f) : Emits ea packCode (fun x=>erasePack (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ((ofProcedure Emission.canonicalPackP).comp hp).congr
    (fun x=>Emission.canonicalPack_erase _ _ (he x))
lemma ofCanonical (hf : Emits ea packCode (fun x=>erasePack (f x))) : NetEmits ea f:=
  ⟨fun x=>erasePack (f x),hf,fun _=>rfl⟩
lemma canonicalLength (hf : NetworkAt (fun x=>(ea x).length) f)
    (hn : PolyAt (fun x=>(ea x).length) n) (hm : PolyAt (fun x=>(ea x).length) m) :
    PolyAt (fun x=>(ea x).length) (fun x=>(packCode (erasePack (f x))).length):=by
  exact ((PolyAt.const _ 104).mul ((((hn.add hf).add hm).add (PolyAt.const _ 1)).pow 2)).of_le
    (fun x=>packCode_bound _)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
