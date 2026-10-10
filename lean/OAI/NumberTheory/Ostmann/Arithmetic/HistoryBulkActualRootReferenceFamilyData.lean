import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkReferenceFrequencyFamily
open HistoryBulkSelectedUniversalOperator HistorySignedXiTransport
open HistoryGiantOriginalMeanFactorization (Choices history)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

variable (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
variable (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
variable {α : Type} [Fintype α] (w : α → ℝ) (P Q : α → ℤ)

variable {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

def Witness.toReference (r : Witness C outside σ a x y J w P Q i) :
    SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2 where
  left := giantState (sourceState C.sources _ (fibreAssignment C a r.bulk) i.1.val)
    (P r.giant) (Q r.giant)
  right := giantState (sourceState C.sources _
    (permuteAssignment C σ (fibreAssignment C a r.bulk)) i.1.val) (P r.giant) (Q r.giant)
  left_frequency := rfl
  right_frequency := rfl
  left_matches := Template.assignedSlots_matches _ _ _
  right_matches := Template.assignedSlots_matches _ _ _
  left_supported := r.supported.1
  right_supported := r.supported.2

def Witness.toActualData (r : Witness C outside σ a x y J w P Q i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l (rightChoices C y i) ≠ 0)
    (hcell : ∀ v, w v ≠ 0 → 0 < P v ∧ 0 < Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)| ≤ 1 ∧
      |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)| ≤ 1) :
    ActualReferenceData C σ i r.toReference where
  assignment := fibreAssignment C a r.bulk
  plus := P r.giant
  minus := Q r.giant
  assignment_mass := (fibreAssignment_mass_pos C a r.bulk ha r.bulk_pos).ne'
  left_choice_mass := hc
  right_choice_mass := he
  plus_pos := (hcell r.giant r.giant_pos.ne').1
  minus_pos := (hcell r.giant r.giant_pos.ne').2.1
  plus_cell := (hcell r.giant r.giant_pos.ne').2.2.1
  minus_cell := (hcell r.giant r.giant_pos.ne').2.2.2
  left_eq := rfl
  right_eq := rfl

end Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily

end

end OAI
