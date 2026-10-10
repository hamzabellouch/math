import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesPermutation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantIntegerReference
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairBulkCoordinates HistoryGiantReferenceMean HistorySignedXiTransport

variable {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k₀ L/2)

def permutedAssignment (C : InitialSourceChoice d Bs BD Bz k₀ L E) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*b₀) k₀) l)) :
    SourceAssignment C.sources (Template.current (Template.initial (2*b₀) k₀) l) :=
  leafBulkAssignmentPermutation b₀ k₀ l C.bulk (C.cells.topSource E C.deleted_card)
    (C.cells.compSource E C.deleted_card) σ x

theorem permutedAssignment_mass (C : InitialSourceChoice d Bs BD Bz k₀ L E) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*b₀) k₀) l)) :
    (assignmentPrior C.sources (Template.current (Template.initial (2*b₀) k₀) l)).mass
      (permutedAssignment C l σ x)=
    (assignmentPrior C.sources (Template.current (Template.initial (2*b₀) k₀) l)).mass x :=
  leafBulkAssignmentPermutation_mass b₀ k₀ l C.bulk (C.cells.topSource E C.deleted_card)
    (C.cells.compSource E C.deleted_card) σ x

def integerMatching (C : InitialSourceChoice d Bs BD Bz k₀ L E) (V : ℕ → ℕ) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*b₀) k₀) l))
    (s t P Q : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*b₀) k₀) V l) :
    RootMatching
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (giantState (sourceState C.sources (Template.current (Template.initial (2*b₀) k₀) l) x s) P Q) c)
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (giantState (sourceState C.sources (Template.current (Template.initial (2*b₀) k₀) l)
          (permutedAssignment C l σ x) t) P Q) e) := by
  apply permutationMatching b₀ k₀ C.bulk (C.cells.topSource E C.deleted_card)
    (C.cells.compSource E C.deleted_card) σ x
  · simpa only [decodeHistory_root,giantState,sourceState] using
      Template.assignedSlots_matches C.sources (Template.current (Template.initial (2*b₀) k₀) l) x
  · simpa only [decodeHistory_root,giantState,sourceState] using
      Template.assignedSlots_matches C.sources (Template.current (Template.initial (2*b₀) k₀) l)
        (permutedAssignment C l σ x)
  · simp only [decodeHistory_root,giantState,sourceState]
    rfl
  · simp only [decodeHistory_root,giantState,sourceState,permutedAssignment]
    rfl

def integerOrderedEquiv (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (V : ℕ → ℕ) (l : ℕ) (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*b₀) k₀) l))
    (s t P Q : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*b₀) k₀) V l)
    (hs : (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
      (giantState (sourceState C.sources (Template.current (Template.initial (2*b₀) k₀) l) x s) P Q) c).Supported V outside) :
    (Fin (2^l) × Fin (2*b₀)) ≃ bulkCoordinates
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (giantState (sourceState C.sources (Template.current (Template.initial (2*b₀) k₀) l) x s) P Q) c)
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (giantState (sourceState C.sources (Template.current (Template.initial (2*b₀) k₀) l)
          (permutedAssignment C l σ x) t) P Q) e) :=
  orderedEquiv (2*b₀) k₀ _ _ hs (by
    simpa only [decodeHistory_root,giantState,sourceState] using
      Template.assignedSlots_matches C.sources (Template.current (Template.initial (2*b₀) k₀) l) x)

theorem integer_rootGiantsAgree (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (V : ℕ → ℕ) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*b₀) k₀) l))
    (s t P Q : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*b₀) k₀) V l) :
    RootGiantsAgree
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (giantState (sourceState C.sources (Template.current (Template.initial (2*b₀) k₀) l) x s) P Q) c)
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (giantState (sourceState C.sources (Template.current (Template.initial (2*b₀) k₀) l)
          (permutedAssignment C l σ x) t) P Q) e) :=
  HistoryGiantXiReplacementActual.decoded_shared_giants _ _ _ _ _ _ _ _ _ _

end Ostmann.Arithmetic.HistoryBulkGiantIntegerReference

end

end OAI
