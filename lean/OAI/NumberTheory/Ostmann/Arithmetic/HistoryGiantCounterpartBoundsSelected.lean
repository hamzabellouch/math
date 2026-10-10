import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCounterpartBoundsBasic
import OAI.NumberTheory.Ostmann.Construction.SelectedCounterpartWindows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCounterpartBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairGiantCoordinates HistoryActiveCoordinates HistoryPairSmoothXi HistoryProductWindows
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k L/2)

theorem selected_remaining_counterpartBounds (C : InitialSourceChoice d Bs BD Bz k L E)
    (s l : ℕ) (hl : l<k) (X : ℝ) (outside : List ℕ) (p : ℕ)
    (u : SourceAssignment C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l)))
    (y : RemainingSample C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant) (v : ℤ)
    (h g : History l) (gs : g.Supported (frequencyBound Bs BD Bz k L) outside)
    (hroot : g.root=remainingState C.sources (Template.current (Template.initial (2*b₀) k) l)
      (l+1) C.giant p u y v)
    (hu : (assignmentPrior C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l))).mass u≠0)
    (hy : (remainingPrior C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant).mass y≠0)
    (hA : actualCoefficient C.sources (Template.initial (2*b₀) k) (frequencyBound Bs BD Bz k L)
      X C.giantCenter (residueTransform d) (sourceStateBins b₀ s C.bulkBin C.spectatorBin)
      outside l (remainingState C.sources (Template.current (Template.initial (2*b₀) k) l)
        (l+1) C.giant p u y v)≠0) :
    CounterpartBounds ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
      (C.compensationLogScale l) (nominalInheritedWidth k l+2) (nominalRemovedWidth k l)
      (pairedDiagonalHKeys h g (l+1)) (pairedDiagonalUKeys h g (l+1))
      (giantCoordinates h g) (pairBackground h g)
      (fun _ => (C.giantCenter:ℝ)-1) (fun _ => (C.giantCenter:ℝ)+1) := by
  have hw := C.remaining_nominal_windows s l hl X outside p u y v hu hy hA
  have hq := (C.remaining_log_support (l+1) l y hy).1
  have hg := History.supported_root_positive gs
  constructor
  · rw [H_endpoint_log_product h g hg,
      diagonalHKeys_product g C.sources _ (l+1) C.giant p u y v hroot]
    have hgminus : g.root.giantMinus=y.1.val := by rw [hroot]; rfl
    rw [hgminus]
    have hh := (abs_le.mp hw.1).1
    have hqq := (abs_le.mp hq).2
    linarith
  · rw [U_endpoint_log_product h g hg,
      diagonalUKeys_product g C.sources _ (l+1) C.giant p u y v hroot]
    have hh := (abs_le.mp hw.2).2
    linarith

end Ostmann.Arithmetic.HistoryGiantCounterpartBounds

end

end OAI
