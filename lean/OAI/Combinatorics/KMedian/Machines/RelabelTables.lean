import Mathlib
import OAI.Combinatorics.KMedian.Machines.RawCSP
import OAI.Combinatorics.KMedian.Amplification.LabelTransport

namespace OAI

section Inline_PCPRelabelTables
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary Binary.Automatic
open scoped Classical

variable {A B V E : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Fintype V] [Fintype E]
noncomputable def relabel (e : A ≃ B) (s : CSPTable A) : CSPTable B :=
  (s.1,s.2.map (fun r => (r.1,r.2.1,r.2.2.map (e.prodCongr e).toEmbedding)))
omit [DecidableEq A] [DecidableEq B] in
lemma poly_relabel (e : A ≃ B) : Poly (relabel e) := by
  have hh : Poly (fun R : Finset (A × A) => R.map (e.prodCongr e).toEmbedding) := hardcoded _
  unfold relabel
  apply Poly.pair Poly.fst
  apply Poly.list_map _ Poly.snd
  exact Poly.pair (Poly.fst.comp Poly.snd)
    (Poly.pair (Poly.fst.comp (Poly.snd.comp Poly.snd))
      (hh.comp (Poly.snd.comp (Poly.snd.comp Poly.snd))))
noncomputable def Represents.relabel {s : CSPTable A} {C : BinaryCSP V E A}
    (r : s.Represents C) (e : A ≃ B) : (s.relabel e).Represents (C.mapLabels e) where
  vertex := r.vertex
  edge := r.edge.trans (finCongr (List.length_map _).symm)
  row j := by
    change (s.2.map _)[(r.edge j).val]=_
    rw [List.getElem_map,r.row]
    rfl
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRelabelTables

end OAI
