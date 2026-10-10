import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}

def paddedListCode (l : List α) (h : l.length ≤ N) (default : α) : Fin N → α :=
  fun i => (l ++ List.replicate (N - l.length) default)[i.val]'(by
    simp only [List.length_append, List.length_replicate]
    omega)

@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI
