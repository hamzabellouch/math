import Mathlib
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β γ : Type}
lemma map_range_getD (xs : List β) (d : β) (f : β→γ) :
    (List.range xs.length).map (fun i=>f ((xs.drop i).headD d))=xs.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_range]
    have hi : i<xs.length:=by simpa using h1
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β→γ}
noncomputable def listMapWith (d : β) (e : γ)
    (p : Procedure (prodCode ea eb) ec (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea (listCode eb)) (listCode ec) (fun x=>x.2.map (f x.1)) := by
  let i:=unaryToBits.comp (first unaryCode (prodCode ea (listCode eb)))
  let env:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp env
  let xs:=(second ea (listCode eb)).comp env
  let get:=(listGet eb d).comp (i.pair xs)
  let step:=p.comp (a.pair get)
  let len:=(NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb))
  exact ((tabulate (f:=fun (env : α×List β) i=>f env.1 ((env.2.drop i).headD d)) e step).comp (len.pair (identity (prodCode ea (listCode eb))))).congrFun (by
    intro x;exact map_range_getD x.2 d (f x.1))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
