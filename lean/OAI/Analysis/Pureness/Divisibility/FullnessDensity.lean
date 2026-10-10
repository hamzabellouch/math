import OAI.Analysis.Pureness.Completion.ClosedIdeals
import OAI.Analysis.Pureness.Operators.FiniteIdealSums
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI
namespace CuntzPureness
open Topology
variable {A : Type*} [NormedRing A] [CompleteSpace A]

theorem exists_invertible_finiteIdealSum (hsimple : TopologicallySimple A)
    (h : A) (hh : h ≠ 0) :
    ∃ l : List (A × A), IsUnit (finiteIdealSum h l) := by
  have h1 : (1 : A) ∈ closure (TwoSidedIdeal.span {h} : Set A) := by
    rw [closure_span_singleton_eq_univ hsimple h hh]
    exact Set.mem_univ _
  have hn : {x : A | IsUnit x} ∈ 𝓝 (1 : A) := Units.isOpen.mem_nhds isUnit_one
  obtain ⟨x, hxunit, hxspan⟩ := mem_closure_iff_nhds.mp h1 _ hn
  obtain ⟨l, hl⟩ := exists_finiteIdealSum hxspan
  exact ⟨l, hl.symm ▸ hxunit⟩
end CuntzPureness

end OAI
