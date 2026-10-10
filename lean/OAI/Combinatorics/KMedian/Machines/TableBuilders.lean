import Mathlib
import OAI.Combinatorics.KMedian.Machines.Ordered
import OAI.Combinatorics.KMedian.Machines.RawCSP

namespace OAI

section Inline_PCPTableBuilders
namespace MetricKMedian.PCP.Compiler
open scoped Classical

namespace Ordered
variable {A B : Type} [DecidableEq A] [DecidableEq B]
def sum (o : Ordered A) (s : Ordered B) : Ordered (A ⊕ B) where
  entries := o.entries.map Sum.inl ++ s.entries.map Sum.inr
  nodup := by
    apply List.Nodup.append (o.nodup.map Sum.inl_injective) (s.nodup.map Sum.inr_injective)
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,h⟩ := List.mem_map.mp hy
    cases h
  all x := by cases x with
    | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a,o.all a,rfl⟩)
    | inr b => exact List.mem_append_right _ (List.mem_map.mpr ⟨b,s.all b,rfl⟩)
end Ordered
namespace CSPTable
variable {V E A : Type} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]
noncomputable def build (C : BinaryCSP V E A) (vo : Ordered V) (eo : Ordered E) : CSPTable A :=
  (vo.entries.map (fun _ => ()),eo.entries.map (fun e => ((vo.equiv (C.left e)).val,(vo.equiv (C.right e)).val,C.allowed e)))
noncomputable def build_represents (C : BinaryCSP V E A) (vo : Ordered V) (eo : Ordered E) :
    (build C vo eo).Represents C where
  vertex := vo.equiv.trans (finCongr (by simp only [build,List.length_map]))
  edge := eo.equiv.trans (finCongr (by simp only [build,List.length_map]))
  row e := by
    change (eo.entries.map (fun j => ((vo.equiv (C.left j)).val,(vo.equiv (C.right j)).val,C.allowed j)))[(eo.equiv e).val]=
      ((vo.equiv (C.left e)).val,(vo.equiv (C.right e)).val,C.allowed e)
    rw [List.getElem_map,Ordered.get_equiv]
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPTableBuilders

end OAI
