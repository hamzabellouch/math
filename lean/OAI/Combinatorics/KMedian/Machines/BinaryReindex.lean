import Mathlib
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPBinaryReindex

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E V' E' A : Type} [DecidableEq A]
variable (C : BinaryCSP V E A) (ev : V ≃ V') (ee : E ≃ E')
def reindex : BinaryCSP V' E' A where
  left e := ev (C.left (ee.symm e))
  right e := ev (C.right (ee.symm e))
  allowed e := C.allowed (ee.symm e)
omit [DecidableEq A]
lemma reindex_satisfies (a : V' → A) :
    (C.reindex ev ee).Satisfies a ↔ C.Satisfies (a ∘ ev) := by
  constructor
  · intro h e
    simpa only [reindex,Equiv.symm_apply_apply,Function.comp_def] using h (ee e)
  · intro h e
    exact h (ee.symm e)
lemma reindex_complete (a : V → A) (h : C.Satisfies a) :
    (C.reindex ev ee).Satisfies (a ∘ ev.symm) := by
  apply (C.reindex_satisfies ev ee _).mpr
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using h
variable [Fintype E] [Fintype E']
lemma reindex_rejection (a : V' → A) :
    (C.reindex ev ee).rejection a=C.rejection (a ∘ ev) := by
  unfold rejection reindex
  exact testRate_equiv ee.symm (fun e => (a (ev (C.left e)),a (ev (C.right e))) ∉ C.allowed e)
end BinaryCSP
end MetricKMedian.PCP

end Inline_PCPBinaryReindex

end OAI
