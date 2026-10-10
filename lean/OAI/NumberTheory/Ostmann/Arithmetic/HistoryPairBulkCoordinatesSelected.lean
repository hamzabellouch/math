import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBoundsSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesPermutation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkCoordinates
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairGiantCoordinates HistoryActiveCoordinates HistorySymbolicEncoding
open HistoryBulkPriorGrid
variable {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k₀ L/2)

def selectedPermutedOuter (C : InitialSourceChoice d Bs BD Bz k₀ L E) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant) :
    OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant :=
  ⟨x.1,x.2.1,leafBulkAssignmentPermutation b₀ k₀ l C.bulk
    (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ x.2.2⟩

theorem selectedPermutedOuter_mass (C : InitialSourceChoice d Bs BD Bz k₀ L E) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant) :
    (outerPrior C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant).mass
      (selectedPermutedOuter C l σ x) =
    (outerPrior C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant).mass x := by
  exact congrArg (fun z => C.giant.law.mass x.1*(C.giant.law.mass x.2.1*z))
    (leafBulkAssignmentPermutation_mass b₀ k₀ l C.bulk
      (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ x.2.2)

def selectedMatching (C : InitialSourceChoice d Bs BD Bz k₀ L E) (V : ℕ → ℕ) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant)
    (s t : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*b₀) k₀) V l) :
    RootMatching
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant x s) c)
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant
          (selectedPermutedOuter C l σ x) t) e) := by
  apply permutationMatching b₀ k₀ C.bulk (C.cells.topSource E C.deleted_card)
    (C.cells.compSource E C.deleted_card) σ x.2.2
  · simpa only [decodeHistory_root, outerState] using
      Template.assignedSlots_matches C.sources (Template.current (Template.initial (2*b₀) k₀) l) x.2.2
  · simpa only [decodeHistory_root, outerState] using
      Template.assignedSlots_matches C.sources (Template.current (Template.initial (2*b₀) k₀) l)
        (selectedPermutedOuter C l σ x).2.2
  · simp only [decodeHistory_root, outerState]
    rfl
  · simp only [decodeHistory_root, outerState, selectedPermutedOuter]
    rfl

theorem selected_bulk_sourceBounds (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (V : ℕ → ℕ) (l : ℕ) (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant)
    (s t : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*b₀) k₀) V l)
    (hx : (outerPrior C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant).mass x ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*b₀) k₀) V l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*b₀) k₀) V l e ≠ 0) :
    let h := decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant x s) c
    let g := decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant
        (selectedPermutedOuter C l σ x) t) e
    h.Supported V outside →
    SourceBounds b₀ k₀ C.giantCenter (C.cells.center b₀) h (leftMap h g)
      (bulkCoordinates h g) (pairBackground h g) (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) ∧
    SourceBounds b₀ k₀ C.giantCenter (C.cells.center b₀) g (rightMap h g)
      (bulkCoordinates h g) (pairBackground h g) (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) := by
  dsimp only
  intro hs
  have hy : (outerPrior C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant).mass
      (selectedPermutedOuter C l σ x) ≠ 0 := by
    rwa [selectedPermutedOuter_mass]
  exact sourceBounds _ _ hs (selectedMatching C V l σ x s t c e)
    (HistoryGiantSourceBounds.selected_decoded_sourceDomain C V l x s c hx hc)
    (HistoryGiantSourceBounds.selected_decoded_sourceDomain C V l
      (selectedPermutedOuter C l σ x) t e hy he) _ _

end Ostmann.Arithmetic.HistoryPairBulkCoordinates

end

end OAI
