import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.InitialAlphabet
import OAI.Combinatorics.KMedian.Machines.AlphabetSpec
import OAI.Combinatorics.KMedian.Machines.TablePromises

namespace OAI

section Inline_PCPInitialTable
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic InitialAlphabet
open scoped Classical

namespace CSPTable
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
noncomputable def pullLabels (f : B→A) (s : CSPTable A) : CSPTable B :=
  (s.1,s.2.map (fun row => (row.1,row.2.1,Finset.univ.filter (fun p => (f p.1,f p.2)∈row.2.2))))
omit [DecidableEq B] in
lemma poly_pullLabels (f : B→A) : Poly (pullLabels f) := by
  have hr : Poly (fun r : Finset (A×A) => Finset.univ.filter (fun p : B×B => (f p.1,f p.2)∈r)) := hardcoded _
  unfold pullLabels
  apply Poly.pair Poly.fst
  apply Poly.list_map _ Poly.snd
  apply Poly.pair (Poly.fst.comp Poly.snd)
  exact Poly.pair (Poly.fst.comp (Poly.snd.comp Poly.snd))
    (hr.comp (Poly.snd.comp (Poly.snd.comp Poly.snd)))
noncomputable def pullRep (f : B→A) (s : CSPTable A) {V E : Type} [Fintype V] [Fintype E]
    {C : BinaryCSP V E A} (r : s.Represents C) : (pullLabels f s).Represents (C.pullLabels f) where
  vertex := r.vertex
  edge := r.edge.trans (finCongr (List.length_map _).symm)
  row e := by
    change (s.2.map _)[(r.edge e).val]=_
    rw [List.getElem_map,r.row]
    rfl
omit [Fintype A] [DecidableEq B] in
lemma pull_wellFormed (f : B→A) {s : CSPTable A} (h : s.WellFormed) : (pullLabels f s).WellFormed := by
  let : Nonempty (Fin s.2.length) := Fin.pos_iff_nonempty.mp h.1
  exact (pullRep f s (self_represents s h)).wellFormed
end CSPTable
namespace InitialProgram
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
noncomputable def bits (s : CSPTable A) := CSPTable.pullLabels (decode A) s
noncomputable def table (s : CSPTable A) := AlphabetProgram.table A (bits A s)
lemma poly_table : Poly (table A) := (AlphabetProgram.poly_table A).comp (CSPTable.poly_pullLabels (decode A))
variable (s : CSPTable A) (h : s.WellFormed)
include h in
lemma bits_valid : (bits A s).WellFormed := CSPTable.pull_wellFormed _ h
noncomputable def bitsRep : (bits A s).Represents (InitialAlphabet.bits A (s.csp h)) :=
  CSPTable.pullRep (decode A) s (CSPTable.self_represents s h)
noncomputable def represents : (table A s).Represents (AlphabetReduction.paddedBinary
    ((bits A s).csp (bits_valid A s h))) := AlphabetProgram.represents A _ _
include h in
lemma valid : (table A s).WellFormed := by
  let : Nonempty (Fin (bits A s).2.length) := Fin.pos_iff_nonempty.mp (bits_valid A s h).1
  exact (represents A s h).wellFormed
lemma correct : (∃ a, ((table A s).csp (valid A s h)).Satisfies a) ↔ ∃ a, (s.csp h).Satisfies a := by
  rw [(represents A s h).satisfies]
  have hb := (bitsRep A s h).satisfies (bits_valid A s h)
  rw [InitialAlphabet.bits_iff] at hb
  constructor
  · rintro ⟨a,ha⟩
    apply hb.mp
    let C := (bits A s).csp (bits_valid A s h)
    refine ⟨AlphabetReduction.decoded C (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed C)),?_⟩
    have hh := AlphabetReduction.padded_sound C a
    rw [(AlphabetReduction.paddedBinary C).rejection_zero_iff _ |>.mpr ha] at hh
    apply (C.rejection_zero_iff _).mp
    have hn := testRate_nonneg (fun e =>
      (AlphabetReduction.decoded C (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed C)) (C.left e),
       AlphabetReduction.decoded C (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed C)) (C.right e))∉C.allowed e)
    change 0≤C.rejection _ at hn
    linarith
  · intro ha
    obtain ⟨a,ha⟩ := hb.mpr ha
    exact AlphabetReduction.padded_complete _ a ha
end InitialProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPInitialTable

end OAI
