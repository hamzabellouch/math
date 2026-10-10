import Mathlib
import OAI.Computability.QuantumFactoring.AIGNetworkEmission

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open BitStackProgram BitStackProgram.Procedure NetworkEmission
open NetworkEmission.Emission
namespace Emission
abbrev dimsCode:=prodCode unaryCode unaryCode
noncomputable def faninPackP : Procedure (prodCode dimsCode NativeAIG.refCode) packCode
    (fun x=>faninPack x.1.1 x.1.2 x.2):=by
  let e:=first dimsCode NativeAIG.refCode
  let n:=(first unaryCode unaryCode).comp e
  let gs:=(second unaryCode unaryCode).comp e
  let w:=unaryAdd.comp (n.pair gs)
  let ref:=second dimsCode NativeAIG.refCode
  let idx:=(first Nat.bits boolCode).comp ref
  let inv:=(second Nat.bits boolCode).comp ref
  let off:=binaryAdd.comp ((unaryToBits.comp n).pair idx)
  let v:=conditional (binaryLt.comp (idx.pair (unaryToBits.comp gs)))
    (bitPackP.comp (w.pair off)) (constantPackP.comp (w.pair (Procedure.constant _ boolCode false)))
  exact (conditional inv (bnotPackP.comp v) v).congrFun (by intro x;simp only [Function.comp_apply,id_eq,decide_eq_true_eq,faninPack])

def declTag : NativeAIG.Decl→ℕ | .zero=>0 | .atom _=>1 | .gate _ _=>2
def declAtom : NativeAIG.Decl→ℕ | .atom i=>i | _=>0
def declGate : NativeAIG.Decl→NativeAIG.Key | .gate a b=>(a,b) | _=>((0,false),(0,false))
noncomputable def declTagP : Procedure NativeAIG.declCode Nat.bits declTag:=
  ((casesSum (Procedure.constant emptyCode Nat.bits 0)
    (casesSum (Procedure.constant Nat.bits Nat.bits 1) (Procedure.constant NativeAIG.keyCode Nat.bits 2))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def declAtomP : Procedure NativeAIG.declCode Nat.bits declAtom:=
  ((casesSum (Procedure.constant emptyCode Nat.bits 0)
    (casesSum (identity Nat.bits) (Procedure.constant NativeAIG.keyCode Nat.bits 0))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def declGateP : Procedure NativeAIG.declCode NativeAIG.keyCode declGate:=
  ((casesSum (Procedure.constant emptyCode NativeAIG.keyCode ((0,false),(0,false)))
    (casesSum (Procedure.constant Nat.bits NativeAIG.keyCode ((0,false),(0,false))) (identity NativeAIG.keyCode))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def nodePackP : Procedure (prodCode dimsCode NativeAIG.declCode) packCode
    (fun x=>nodePack x.1.1 x.1.2 x.2):=by
  let e:=first dimsCode NativeAIG.declCode
  let w:=unaryAdd.comp e
  let d:=second dimsCode NativeAIG.declCode
  let tag:=declTagP.comp d
  let z:=constantPackP.comp (w.pair (Procedure.constant _ boolCode false))
  let a:=bitPackP.comp (w.pair (declAtomP.comp d))
  let l:=(first NativeAIG.refCode NativeAIG.refCode).comp (declGateP.comp d)
  let r:=(second NativeAIG.refCode NativeAIG.refCode).comp (declGateP.comp d)
  let g:=bandPackP.comp ((faninPackP.comp (e.pair l)).pair (faninPackP.comp (e.pair r)))
  exact (conditional (binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits 0))) z
    (conditional (binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits 1))) a g)).congrFun (by
      rintro ⟨e,d⟩;cases d <;> rfl)

abbrev graphInputCode:=prodCode unaryCode (listCode NativeAIG.declCode)
noncomputable def partialPackP : Procedure (prodCode graphInputCode unaryCode) packCode
    (fun x=>partialPack x.1.1 x.1.2 x.2):=by
  let e:=second unaryCode graphInputCode
  let n:=(first unaryCode (listCode NativeAIG.declCode)).comp e
  let ds:=(second unaryCode (listCode NativeAIG.declCode)).comp e
  let gs:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ds
  let w:=unaryAdd.comp (n.pair gs)
  let i:=first unaryCode graphInputCode
  let off:=binaryAdd.comp ((unaryToBits.comp n).pair (unaryToBits.comp i))
  let d:=(listGet NativeAIG.declCode .zero).comp ((unaryToBits.comp i).pair ds)
  let node:=nodePackP.comp ((n.pair gs).pair d)
  let step:=assignPackP.comp (w.pair (off.pair node))
  let input:=first graphInputCode unaryCode
  let num:=second graphInputCode unaryCode
  let parts:=(tabulate (f:=fun (x:ℕ×List NativeAIG.Decl) i=>assignPack (x.1+x.2.length) (x.1+i)
    (nodePack x.1 x.2.length ((x.2.drop i).headD .zero))) emptyPack step).comp (num.pair input)
  let nn:=(first unaryCode (listCode NativeAIG.declCode)).comp input
  let gg:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ((second unaryCode (listCode NativeAIG.declCode)).comp input)
  exact foldCompP.comp (parts.pair (identityPackP.comp (unaryAdd.comp (nn.pair gg))))
noncomputable def padPackP : Procedure dimsCode packCode (fun x=>padPack x.1 x.2):=by
  let e:=second unaryCode dimsCode
  let n:=(first unaryCode unaryCode).comp e
  let i:=unaryToBits.comp (first unaryCode dimsCode)
  let v:=conditional (binaryLt.comp (i.pair (unaryToBits.comp n)))
    (bitPackP.comp (n.pair i)) (constantPackP.comp (n.pair (Procedure.constant _ boolCode false)))
  let parts:=(tabulate (f:=fun (x:ℕ×ℕ) i=>if i<x.1 then bitPack x.1 i else constantPack x.1 false)
    emptyPack (v.congrFun (by intro x;simp only [Function.comp_apply,id_eq,decide_eq_true_eq]))).comp (unaryAdd.pair (identity dimsCode))
  exact vectorPackP.comp ((first unaryCode unaryCode).pair parts)
noncomputable def compilePackP : Procedure (prodCode graphInputCode (listCode NativeAIG.refCode)) packCode
    (fun x=>compilePack x.1.1 x.1.2 x.2):=by
  let e:=first graphInputCode (listCode NativeAIG.refCode)
  let n:=(first unaryCode (listCode NativeAIG.declCode)).comp e
  let ds:=(second unaryCode (listCode NativeAIG.declCode)).comp e
  let gs:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ds
  let dim:=n.pair gs
  let pad:=padPackP.comp dim
  let graph:=partialPackP.comp (e.pair gs)
  let refs:=second graphInputCode (listCode NativeAIG.refCode)
  let parts:=(listMapWith (f:=fun (x:ℕ×ℕ) f=>faninPack x.1 x.2 f) (0,false) emptyPack faninPackP).comp (dim.pair refs)
  let output:=vectorPackP.comp ((unaryAdd.comp dim).pair parts)
  exact compPackP.comp ((compPackP.comp (pad.pair graph)).pair output)
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

end



end OAI
