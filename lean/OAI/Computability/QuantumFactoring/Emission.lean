import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGFullAdder

namespace OAI

section
namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

namespace Emission
open BitStackProgram BitStackProgram.Procedure
def tripleCode : Triple→List Bool:=prodCode refCode (prodCode refCode refCode)
noncomputable def fullOutP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>fullOut x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let a:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let b:=(first refCode refCode).comp bc
  let c:=(second refCode refCode).comp bc
  let s:=xorP.comp (r.pair (a.pair b))
  exact (xorP.comp (((first graphCode refCode).comp s).pair
    (((second graphCode refCode).comp s).pair c))).congrFun (by intro x;rfl)
noncomputable def fullCarryP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>fullCarry x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let a:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let b:=(first refCode refCode).comp bc
  let c:=(second refCode refCode).comp bc
  let s:=xorP.comp (r.pair (a.pair b))
  let t:=gateP.comp (((first graphCode refCode).comp s).pair
    (((second graphCode refCode).comp s).pair c))
  let u:=gateP.comp (((first graphCode refCode).comp t).pair (a.pair b))
  exact (orP.comp (((first graphCode refCode).comp u).pair
    (((second graphCode refCode).comp t).pair ((second graphCode refCode).comp u)))).congrFun (by intro x;rfl)
noncomputable def fullP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode keyCode)
    (fun x=>full x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let o:=fullOutP
  let abc:=second graphCode tripleCode
  let k:=fullCarryP.comp (((first graphCode refCode).comp o).pair abc)
  exact (((first graphCode refCode).comp k).pair
    (((second graphCode refCode).comp o).pair ((second graphCode refCode).comp k))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
