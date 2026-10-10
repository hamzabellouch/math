import Mathlib
import OAI.Computability.QuantumFactoring.NetworkModularEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
lemma modularPower_emission : NetEmits (prodCode unaryCode unaryCode) (fun x=>modularPower x.1 x.2):=by
  obtain ⟨p,hp,ep⟩:=powerStep_emission
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode unaryCode)
  have hw:=hx.fst
  have hb:=hx.snd
  have hI:=((hw.unaryAdd hw).unaryAdd hb)
  have hW:=hI.unaryAdd hw
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hb.pair hx)
  let q:=fun wb k=>((List.range k).map (p wb)).foldl compPack (identityPack (powerWidth wb.1 wb.2))
  have hq : Emits (prodCode unaryCode unaryCode) packCode (fun wb=>q wb wb.2):=
    (ofProcedure Emission.foldCompP).comp (hps.pair ((ofProcedure Emission.identityPackP).comp hW))
  have eq : ∀w b k (hk:k ≤ b),(q (w,b) k).val.value=erase (powerPrefix w b k hk):=by
    intro w b k
    induction k with
    | zero=>intro hk;exact identityPack_value _
    | succ k ih=>
      intro hk
      dsimp only [q]
      rw [List.range_succ,List.map_append,List.foldl_append,List.map_singleton,List.foldl_cons,List.foldl_nil]
      exact compPack_spec _ _ _ _ (ih (by omega)) (ep w b ⟨k,by omega⟩)
  have hprefix : NetEmits (prodCode unaryCode unaryCode) (fun x=>powerPrefix x.1 x.2 x.2 le_rfl):=
    ⟨fun x=>q x x.2,hq,fun x=>eq x.1 x.2 x.2 le_rfl⟩
  have hstart:= (NetEmits.identity hI).pair (NetEmits.wordConst hI hw (const _ _ 1))
  exact hstart.comp (hprefix.rewireSlice hw hI.unaryNat _ (by intros;rfl))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {w b : α→ℕ}
lemma modularPower (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BitArithmetic.modularPower (w x) (b x)):=by
  obtain ⟨pack, hpack, hvalue⟩ := modularPower_emission
  exact ⟨fun value => pack (w value, b value),
    hpack.comp (hw.pair hb), fun value => hvalue (w value, b value)⟩
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
