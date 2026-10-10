import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesMatching
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesOrder
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkTransport
open Construction Construction.CanonicalOccurrenceTransport HistorySymbolicEncoding
open HistoryPairPattern HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryPairBulkCoordinates
open HistoryOccurrenceVariables
attribute [local instance] Classical.propDecidable

@[simp] theorem assigned_internal_sample (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l)) (c : HistoryChoices sources seed V l)
    (i : Internal seed l) :
    coordinateSample seed (assignedHistory sources seed V l s gp gm x c)
      (assignedLabels sources seed V l s gp gm x c) (.inr (.inr i)) =
        (historyDraws sources seed V l c i).val :=
  decoded_coordinateSample_internal sources seed V l _ c (assignedRoot_matches sources _ s gp gm x) i

variable (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
  (s t : ℤ) (gp gm : ℕ)
  (x x' : SourceAssignment sources (Template.current seed l))
  (σ : Equiv.Perm (Fin (Template.current seed l).length))
  (hσ : ∀ i, sources ((Template.current seed l).get (σ i)).origin = sources ((Template.current seed l).get i).origin)
  (c d : HistoryChoices sources seed V l)
local notation "H" => assignedHistory sources seed V l s gp gm x c
local notation "K" => assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d
local notation "H'" => assignedHistory sources seed V l s gp gm x' c
local notation "K'" => assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d
local notation "AH" => assignedLabels sources seed V l s gp gm x c
local notation "AK" => assignedLabels sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d
local notation "AH'" => assignedLabels sources seed V l s gp gm x' c
local notation "AK'" => assignedLabels sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d

theorem assigned_right_root_key (i : Fin (Template.current seed l).length) :
    rightMap H K (coordinateEquiv seed K AK (.inr (.inl i))) =
      leftMap H K (coordinateEquiv seed H AH (.inr (.inl (σ i)))) := by
  apply Subtype.ext
  change Sum.inr (l+1, coordinateSample seed K AK (.inr (.inl i))) =
    Sum.inr (l+1, coordinateSample seed H AH (.inr (.inl (σ i))))
  rw [assigned_root_sample, assigned_root_sample, Conclusion.sourceAssignmentPermutation_val]

theorem assigned_nonbulk_of_not_mem (i : Fin (Template.current seed l).length)
    (hi : leftMap H K (coordinateEquiv seed H AH (.inr (.inl i))) ∉ bulkCoordinates H K) :
    ((Template.current seed l).get i).role ≠ .bulk := by
  intro hr
  apply hi
  apply Finset.mem_image.mpr
  refine ⟨⟨matchedRootPosition (root_matches AH) i, ?_⟩, Finset.mem_univ _, rfl⟩
  exact (matchedRootPosition_role (root_matches AH) i).trans hr

variable (hs : (assignedHistory sources seed V l s gp gm x c).Supported V outside)
  (hs' : (assignedHistory sources seed V l s gp gm x' c).Supported V outside)

def assignedBulkEquiv (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) (s t : ℤ) (gp gm : ℕ)
    (x x' : SourceAssignment sources (Template.current seed l))
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀ i, sources ((Template.current seed l).get (σ i)).origin =
      sources ((Template.current seed l).get i).origin)
    (c d : HistoryChoices sources seed V l)
    (hs : (assignedHistory sources seed V l s gp gm x c).Supported V outside) (hs' : (assignedHistory sources seed V l s gp gm x' c).Supported V outside) :
    PairKey (assignedHistory sources seed V l s gp gm x c) (assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d) ≃ PairKey (assignedHistory sources seed V l s gp gm x' c) (assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d) :=
  pairKeyEquiv seed (assignedHistory sources seed V l s gp gm x c) (assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d) (assignedHistory sources seed V l s gp gm x' c) (assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d)
    (assignedLabels sources seed V l s gp gm x c)
    (assignedLabels sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d)
    (assignedLabels sources seed V l s gp gm x' c)
    (assignedLabels sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d)
    (samePairPattern_assigned sources seed V outside l s t gp gm gp gm x x' σ hσ c d c d hs hs' rfl)

local notation "E" => assignedBulkEquiv sources seed V outside l s t gp gm x x' σ hσ c d hs hs'

include hs hs' in
@[simp] theorem assignedBulkEquiv_left (i : Coordinate seed l) :
    E (leftMap H K (coordinateEquiv seed H AH i)) =
      leftMap H' K' (coordinateEquiv seed H' AH' i) :=
  pairKeyEquiv_left seed H K H' K' AH AK AH' AK' _ i

include hs hs' in
@[simp] theorem assignedBulkEquiv_right (i : Coordinate seed l) :
    E (rightMap H K (coordinateEquiv seed K AK i)) =
      rightMap H' K' (coordinateEquiv seed K' AK' i) :=
  pairKeyEquiv_right seed H K H' K' AH AK AH' AK' _ i

variable (hfixed : ∀ i, ((Template.current seed l).get i).role ≠ .bulk → (x' i).val = (x i).val)

include hs hs' hfixed in
theorem assigned_background_left_nonbulk (i : Fin (Template.current seed l).length)
    (hi : leftMap H K (coordinateEquiv seed H AH (.inr (.inl i))) ∉ bulkCoordinates H K) :
    pairBackground H' K' (E (leftMap H K (coordinateEquiv seed H AH (.inr (.inl i))))) =
      pairBackground H K (leftMap H K (coordinateEquiv seed H AH (.inr (.inl i)))) := by
  rw [assignedBulkEquiv_left]
  change (coordinateSample seed H' AH' (.inr (.inl i)) : ℝ) =
    (coordinateSample seed H AH (.inr (.inl i)) : ℝ)
  rw [assigned_root_sample, assigned_root_sample]
  exact_mod_cast hfixed i (assigned_nonbulk_of_not_mem sources seed V l s t gp gm x σ hσ c d i hi)

include hs hs' hfixed in

theorem assigned_background_frozen (j : PairKey H K) (hj : j ∉ bulkCoordinates H K) :
    pairBackground H' K' (E j) = pairBackground H K j := by
  obtain ⟨i, rfl⟩ := canonicalPairMap_surjective seed H K AH AK j
  rcases i with (b | i | i) | (b | i | i) <;>
    simp only [canonicalPairMap, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] at *
  · rw [assignedBulkEquiv_left]
    cases b
    · change ((H').root.giantPlus : ℝ) = ((H).root.giantPlus : ℝ)
      simp [assignedHistory, decodeHistory_root, assignedRoot]
    · change ((H').root.giantMinus : ℝ) = ((H).root.giantMinus : ℝ)
      simp [assignedHistory, decodeHistory_root, assignedRoot]
  · exact assigned_background_left_nonbulk sources seed V outside l s t gp gm x x' σ hσ c d hs hs' hfixed i hj
  · rw [assignedBulkEquiv_left]
    change (coordinateSample seed H' AH' (.inr (.inr i)) : ℝ) =
      (coordinateSample seed H AH (.inr (.inr i)) : ℝ)
    rw [assigned_internal_sample, assigned_internal_sample]
  · rw [assignedBulkEquiv_right]
    cases b
    · change ((H').root.giantPlus : ℝ) = ((H).root.giantPlus : ℝ)
      simp [assignedHistory, decodeHistory_root, assignedRoot]
    · change ((H').root.giantMinus : ℝ) = ((H).root.giantMinus : ℝ)
      simp [assignedHistory, decodeHistory_root, assignedRoot]
  · rw [assigned_right_root_key] at hj ⊢
    exact assigned_background_left_nonbulk sources seed V outside l s t gp gm x x' σ hσ c d hs hs' hfixed (σ i) hj
  · rw [assignedBulkEquiv_right]
    change (coordinateSample seed K' AK' (.inr (.inr i)) : ℝ) =
      (coordinateSample seed K AK (.inr (.inr i)) : ℝ)
    rw [assigned_internal_sample, assigned_internal_sample]

include hs hs' hfixed in

theorem assigned_background_eq_insert :
    (pairBackground H' K') ∘ E =
      HistoryActiveCoordinates.insert (bulkCoordinates H K) (pairBackground H K)
        (fun i => pairBackground H' K' (E i.val)) := by
  funext j
  by_cases hj : j ∈ bulkCoordinates H K
  · simp only [Function.comp_apply, HistoryActiveCoordinates.insert, dite_eq_left hj]
  · simp only [Function.comp_apply, HistoryActiveCoordinates.insert, dite_eq_right hj]
    exact assigned_background_frozen sources seed V outside l s t gp gm x x' σ hσ c d hs hs' hfixed j hj

end Ostmann.Arithmetic.HistoryPairBulkTransport

end

end OAI
