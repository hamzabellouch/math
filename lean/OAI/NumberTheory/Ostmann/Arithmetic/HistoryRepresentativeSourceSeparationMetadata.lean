import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentatives
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistory
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSources
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation
open scoped BigOperators
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding

lemma internalSource_mem_seed (seed : List SourceSlot) {l : ℕ} (i : Internal seed l) :
    internalSource seed i∈seed := by
  induction l with
  | zero => exact Empty.elim i
  | succ l ih =>
    rcases i with i | i | i
    · exact Template.mem_extracted_current_mem_seed (List.get_mem _ i)
    · exact ih i
    · exact ih i

theorem internalSlot_source_mem (seed : List SourceSlot) {l : ℕ} (h : History l)
    (hh : TreeSourceLabels seed h) (i : InternalKey h) : sourceOfSlot (internalSlot h i)∈seed := by
  obtain ⟨j,rfl⟩ := (internalEquiv seed h hh).surjective i
  rw [internalEquiv_source]
  exact internalSource_mem_seed seed j

theorem rootSlot_source_mem (seed : List SourceSlot) {l : ℕ} (h : History l)
    (hh : TreeSourceLabels seed h) (i : Fin h.root.small.length) :
    sourceOfSlot (h.root.small.get i)∈seed := by
  let e := finCongr (Template.matches_length (root_matches hh)).symm
  obtain ⟨j,rfl⟩ := e.surjective i
  rw [matches_get_source (root_matches hh)]
  exact Template.mem_current_mem_seed (List.get_mem _ j)

theorem decoded_internalSlot_mass (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (hc : choicesMass sources seed V l c≠0)
    (i : InternalKey (decodeHistory sources seed V l a c)) :
    sourceMass sources (internalSlot (decodeHistory sources seed V l a c) i)≠0 := by
  have hp : (∏i : InternalKey (decodeHistory sources seed V l a c),
      sourceMass sources (internalSlot (decodeHistory sources seed V l a c) i))≠0 := by
    rw [prod_internalSlot,←History.internalMass_eq_occurrences,decodeHistory_internalMass]
    exact hc
  exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)

end Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation

end

end OAI
