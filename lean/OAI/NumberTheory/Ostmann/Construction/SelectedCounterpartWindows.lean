import OAI.NumberTheory.Ostmann.Construction.CounterpartCutoff
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportCells
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportCenters

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Conclusion Arithmetic.HistoryProductWindows
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k L/2)

def compensationLogScale (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) : ℝ :=
  (2:ℝ)^l*nominalWeight k
    (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin) (stepGap BD Bz k L) l

theorem remaining_nominal_windows (C : InitialSourceChoice d Bs BD Bz k L E)
    (s l : ℕ) (hl : l<k) (X : ℝ) (outside : List ℕ) (p : ℕ)
    (u : SourceAssignment C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l)))
    (y : RemainingSample C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant) (v : ℤ)
    (hu : (assignmentPrior C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l))).mass u≠0)
    (hy : (remainingPrior C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant).mass y≠0)
    (hA : actualCoefficient C.sources (Template.initial (2*b₀) k) (frequencyBound Bs BD Bz k L)
      X C.giantCenter (residueTransform d) (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin)
      outside l (remainingState C.sources (Template.current (Template.initial (2*b₀) k) l)
        (l+1) C.giant p u y v)≠0) :
    |Real.log (remainingProduct C.sources (Template.remainder (l+1)
        (Template.current (Template.initial (2*b₀) k) l)) C.giant y:ℝ)-
      ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)|≤nominalInheritedWidth k l ∧
    |Real.log (((assignedSlots C.sources (Template.extracted (l+1)
        (Template.current (Template.initial (2*b₀) k) l)) u).map SmallSlot.value).prod:ℝ)-
      C.compensationLogScale l|≤nominalRemovedWidth k l := by
  let T := Template.current (Template.initial (2*b₀) k) l
  let us := assignedSlots C.sources (Template.extracted (l+1) T) u
  let ys := assignedSlots C.sources (Template.remainder (l+1) T) y.2
  let a := remainingState C.sources T (l+1) C.giant p u y v
  let J := nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin
  let w := nominalWeight k J (stepGap BD Bz k L)
  have hum := Template.assignedSlots_matches C.sources (Template.extracted (l+1) T) u
  have hym := Template.assignedSlots_matches C.sources (Template.remainder (l+1) T) y.2
  have hur := assignedSlots_extracted_roles C.sources T (l+1) u
  have hup := fun z hz => (assignedSlots_prime C.sources (Template.extracted (l+1) T) u z hz).pos
  have hyp := fun z hz => (assignedSlots_prime C.sources (Template.remainder (l+1) T) y.2 z hz).pos
  have hcells := C.remaining_log_support (l+1) l y hy
  have hcellu := C.extracted_log_support (l+1) l u hu
  constructor
  · apply inherited_window_normalize b₀ k l _ C.giantCenter C.bulkBin J (stepGap BD Bz k L l) w
      (C.cells.center b₀) _ (C.top_frequency_center_error b₀)
      (C.type_frequency_center_error b₀) (nominalWeight_recurrence_scaled hl J (stepGap BD Bz k L))
    exact actualCoefficient_remaining_window C.sources b₀ s k l (frequencyBound Bs BD Bz k L)
      X C.giantCenter C.bulkBin C.spectatorBin (residueTransform d) outside a us ys y.1.val
      (C.cells.center b₀) (Template.reinsert_matches (l+1) T us ys hum hym) hA
      (Template.reinsert_perm (l+1) T us ys (assignedSlots_length _ _ _) (assignedSlots_length _ _ _))
      hur hym (C.giant.prime _ y.1.property).pos hyp hcells.1 hcells.2
  · apply removed_window_normalize b₀ k l hl _ w (C.cells.center b₀) _
      (C.type_frequency_center_error b₀)
    exact integer_removed_window b₀ k l us (C.cells.center b₀) hur hum hup hcellu

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
