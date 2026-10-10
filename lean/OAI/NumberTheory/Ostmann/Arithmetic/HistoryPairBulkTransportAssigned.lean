import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportDecoded

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkTransport
open Construction Construction.CanonicalOccurrenceTransport HistorySymbolicEncoding
open HistoryPairPattern HistoryPairSmoothXi

def assignedRoot (sources : SourceFamily) (T : List SourceSlot) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources T) : State := ⟨s, gp, gm, assignedSlots sources T x⟩

theorem assignedRoot_matches (sources : SourceFamily) (T : List SourceSlot) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources T) : Template.Matches T (assignedRoot sources T s gp gm x).small :=
  Template.assignedSlots_matches sources T x

def assignedHistory (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (s : ℤ) (gp gm : ℕ) (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) : History l :=
  decodeHistory sources seed V l (assignedRoot sources (Template.current seed l) s gp gm x) c

theorem assignedLabels (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (s : ℤ) (gp gm : ℕ) (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) : TreeSourceLabels seed (assignedHistory sources seed V l s gp gm x c) :=
  decoded_tree_source_labels sources seed V l _ c (assignedRoot_matches sources _ s gp gm x)

@[simp] theorem assigned_root_sample (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l)) (c : HistoryChoices sources seed V l)
    (i : Fin (Template.current seed l).length) :
    coordinateSample seed (assignedHistory sources seed V l s gp gm x c)
      (assignedLabels sources seed V l s gp gm x c) (.inr (.inl i)) = (x i).val :=
  coordinateSample_root_assigned sources seed V l _ c x rfl (assignedRoot_matches sources _ s gp gm x) i

variable (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x x' : SourceAssignment sources (Template.current seed l))
  (σ : Equiv.Perm (Fin (Template.current seed l).length))
  (hσ : ∀ i, sources ((Template.current seed l).get (σ i)).origin = sources ((Template.current seed l).get i).origin)
  (c d c' d' : HistoryChoices sources seed V l)

theorem samePairPattern_assigned
    (hs : (assignedHistory sources seed V l s gp gm x c).Supported V outside)
    (hs' : (assignedHistory sources seed V l s gp' gm' x' c').Supported V outside)
    (hpattern : pairedDrawPattern sources seed V l c d = pairedDrawPattern sources seed V l c' d') :
    SamePairPattern seed
      (assignedHistory sources seed V l s gp gm x c)
      (assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d)
      (assignedHistory sources seed V l s gp' gm' x' c')
      (assignedHistory sources seed V l t gp' gm' (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d')
      (assignedLabels sources seed V l s gp gm x c)
      (assignedLabels sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d)
      (assignedLabels sources seed V l s gp' gm' x' c')
      (assignedLabels sources seed V l t gp' gm' (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d') := by
  apply samePairPattern_decoded sources seed V outside l _ _ _ _ c d c' d'
    (assignedRoot_matches sources _ s gp gm x)
    (assignedRoot_matches sources _ t gp gm _)
    (assignedRoot_matches sources _ s gp' gm' x')
    (assignedRoot_matches sources _ t gp' gm' _) hs hs' σ
  · intro i
    exact (assigned_root_sample sources seed V l t gp gm
      (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d i).trans
      ((congrArg (fun n : ℕ => (n : ℤ))
        (Conclusion.sourceAssignmentPermutation_val sources _ σ hσ x i)).trans
        (assigned_root_sample sources seed V l s gp gm x c (σ i)).symm)
  · intro i
    exact (assigned_root_sample sources seed V l t gp' gm'
      (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d' i).trans
      ((congrArg (fun n : ℕ => (n : ℤ))
        (Conclusion.sourceAssignmentPermutation_val sources _ σ hσ x' i)).trans
        (assigned_root_sample sources seed V l s gp' gm' x' c' (σ i)).symm)
  · exact hpattern

theorem assigned_pairedRealXi_eq
    (hs : (assignedHistory sources seed V l s gp gm x c).Supported V outside)
    (ks : (assignedHistory sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d).Supported V outside)
    (hs' : (assignedHistory sources seed V l s gp' gm' x' c').Supported V outside)
    (ks' : (assignedHistory sources seed V l t gp' gm' (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d').Supported V outside)
    (hpattern : pairedDrawPattern sources seed V l c d = pairedDrawPattern sources seed V l c' d')
    (hfreq : historyFrequencies sources seed V l c = historyFrequencies sources seed V l c')
    (hfreq' : historyFrequencies sources seed V l d = historyFrequencies sources seed V l d')
    (bcount scount : ℕ) (X tb td G : ℝ)
    (y : PairKey (assignedHistory sources seed V l s gp' gm' x' c')
      (assignedHistory sources seed V l t gp' gm' (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d') → ℝ) :
    let hp := samePairPattern_assigned sources seed V outside l s t gp gm gp' gm' x x' σ hσ c d c' d' hs hs' hpattern
    pairedRealXi bcount scount X tb td G _ _ hs ks
      (y ∘ pairKeyEquiv seed _ _ _ _
        (assignedLabels sources seed V l s gp gm x c)
        (assignedLabels sources seed V l t gp gm (Conclusion.sourceAssignmentPermutation sources _ σ hσ x) d)
        (assignedLabels sources seed V l s gp' gm' x' c')
        (assignedLabels sources seed V l t gp' gm' (Conclusion.sourceAssignmentPermutation sources _ σ hσ x') d') hp) =
      pairedRealXi bcount scount X tb td G _ _ hs' ks' y := by
  dsimp only
  exact decoded_pairedRealXi_eq sources seed V outside l _ _ _ _ c d c' d'
    (assignedRoot_matches sources _ s gp gm x) (assignedRoot_matches sources _ t gp gm _)
    (assignedRoot_matches sources _ s gp' gm' x') (assignedRoot_matches sources _ t gp' gm' _)
    rfl rfl hfreq hfreq' hs ks hs' ks'
    (samePairPattern_assigned sources seed V outside l s t gp gm gp' gm' x x' σ hσ c d c' d' hs hs' hpattern)
    bcount scount X tb td G y

end Ostmann.Arithmetic.HistoryPairBulkTransport

end

end OAI
