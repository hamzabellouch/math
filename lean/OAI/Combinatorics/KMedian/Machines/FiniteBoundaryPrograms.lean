import Mathlib
import OAI.Combinatorics.KMedian.Machines.FiniteFilterProgram

namespace OAI

section Inline_PCPFiniteBoundaryPrograms
namespace MetricKMedian.PCP.Compiler.FiniteList
open Binary Binary.Automatic
open scoped Classical

variable {X I A : Type} [Coding X] [Fintype I] [Coding (Finset I)] [Fintype A] [Coding A] [Hardcoded A] [Inhabited A]
lemma poly_prefixFilter (pref : X→List A) (bound : X→ℕ) (v : I→Option A)
    (hp : Poly pref) (hb : Poly bound) :
    Poly (fun p : X×ℕ=>Finset.univ.filter (fun i=>Tableau.prefixCell (pref p.1) (bound p.1) p.2 (v i))) := by
  exact poly_finite_filter _ (fun i=>poly_prefixCell pref bound (v i) hp hb)
lemma poly_getFilter (pref : X→List A) (v : I→Option A) (hp : Poly pref) :
    Poly (fun p : X×ℕ=>Finset.univ.filter (fun i=>v i=(pref p.1)[p.2]?)) := by
  have hh : Poly (fun a : Option A=>Finset.univ.filter (fun i=>v i=a)) := hardcoded _
  exact hh.comp (poly_getElem?.comp (Poly.pair (hp.comp Poly.fst) Poly.snd))
end MetricKMedian.PCP.Compiler.FiniteList

end Inline_PCPFiniteBoundaryPrograms

end OAI
