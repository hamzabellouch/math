import Mathlib
import OAI.Combinatorics.KMedian.Machines.FiniteCompiler

namespace OAI

section Inline_PCPListAllProgram
namespace MetricKMedian.Binary.Automatic.Poly
open scoped Classical

lemma list_all {X A : Type} [Coding X] [Coding A] [Inhabited X] [Inhabited A]
    {f : X→A→Bool} {xs : X→List A} (hf : Poly (fun z : X×A=>f z.1 z.2))
    (hx : Poly xs) : Poly (fun x=>(xs x).all (f x)) := by
  have hh := list_empty.comp (list_filter (f:=fun x a=>!f x a) (bool_not.comp hf) hx)
  apply MetricKMedian.PCP.Compiler.poly_congr hh
  intro x
  rw [Bool.eq_iff_iff]
  simp only [List.isEmpty_iff,List.filter_eq_nil_iff,Bool.not_eq_true_eq_eq_false,
    Bool.not_eq_false,List.all_eq_true]
end MetricKMedian.Binary.Automatic.Poly

end Inline_PCPListAllProgram

end OAI
