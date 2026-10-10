import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkCoordinates
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairGiantCoordinates HistoryActiveCoordinates HistoryBulkPriorGrid
variable {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k₀ L/2)

def selectedOrderedEquiv (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (V : ℕ → ℕ) (l : ℕ) (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant)
    (s t : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*b₀) k₀) V l)
    (hs : (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant x s) c).Supported V outside) :
    (Fin (2^l) × Fin (2*b₀)) ≃ bulkCoordinates
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant x s) c)
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant
          (selectedPermutedOuter C l σ x) t) e) :=
  orderedEquiv (2*b₀) k₀ _ _ hs (by
    simpa only [decodeHistory_root, outerState] using
      Template.assignedSlots_matches C.sources (Template.current (Template.initial (2*b₀) k₀) l) x.2.2)

theorem selected_bulk_sample_log_bounds (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (l : ℕ)
    (x : OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant)
    (u : Fin (2^l) × Fin (2*b₀)) :
    bulkLogLower L < Real.log (((x.2.2 ((currentBulkPositionEquiv (2*b₀) k₀ l).symm u).val).val : ℕ) : ℝ) ∧
      Real.log (((x.2.2 ((currentBulkPositionEquiv (2*b₀) k₀ l).symm u).val).val : ℕ) : ℝ) ≤ bulkLogUpper L := by
  let i := (currentBulkPositionEquiv (2*b₀) k₀ l).symm u
  have hs : C.sources ((Template.current (Template.initial (2*b₀) k₀) l)[i.val].origin) = C.bulk :=
    current_bulk_source b₀ k₀ l C.bulk (C.cells.topSource E C.deleted_card)
      (C.cells.compSource E C.deleted_card) i
  have hm : (x.2.2 i.val).val ∈ C.bulk.candidates := by
    rw [← hs]
    exact (x.2.2 i.val).property
  have hp := (mem_bulkPrimeBand L E (x.2.2 i.val).val).mp hm
  exact ⟨hp.2.1,hp.2.2.1⟩

theorem selected_rootGiantsAgree (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (V : ℕ → ℕ) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b₀)))
    (x : OuterSample C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant)
    (s t : ℤ) (c e : HistoryChoices C.sources (Template.initial (2*b₀) k₀) V l) :
    RootGiantsAgree
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant x s) c)
      (decodeHistory C.sources (Template.initial (2*b₀) k₀) V l
        (outerState C.sources (Template.current (Template.initial (2*b₀) k₀) l) C.giant
          (selectedPermutedOuter C l σ x) t) e) := by
  constructor <;> simp only [decodeHistory_root, outerState, selectedPermutedOuter]

end Ostmann.Arithmetic.HistoryPairBulkCoordinates

end

end OAI
