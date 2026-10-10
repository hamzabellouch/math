import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexCoordinates
import OAI.NumberTheory.Ostmann.Construction.SelectedCounterpartBound

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
namespace InitialSourceChoice
open Conclusion Arithmetic.HistoryProductWindows
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k L/2)

theorem counterpart_bound_of_first_coefficient (C : InitialSourceChoice d Bs BD Bz k L E)
    (s l : ℕ) (hl : l<k) (X : ℝ) (outside : List ℕ) (p : ℕ)
    (u : SourceAssignment C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l)))
    (x : RemainingSample C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant) (v : ℤ)
    (hu : (assignmentPrior C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l))).mass u≠0)
    (hx : (remainingPrior C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant).mass x≠0)
    (hA : actualCoefficient C.sources (Template.initial (2*b₀) k) (frequencyBound Bs BD Bz k L)
      X C.giantCenter (residueTransform d) (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin)
      outside l (remainingState C.sources (Template.current (Template.initial (2*b₀) k) l)
        (l+1) C.giant p u x v)≠0)
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l))))
    (he : CounterpartCompatible C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant x e) :
    let y := reconstructCounterpart C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant x e he
    let K := remainingCounterpart C.sources (Template.current (Template.initial (2*b₀) k) l)
      (l+1) C.giant ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
      (C.compensationLogScale l) C.giantCenter (C.cells.center b₀) u y
    0≤K ∧ K≤Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l) := by
  have hw := C.remaining_nominal_windows s l hl X outside p u x v hu hx hA
  apply remainingCounterpart_le C.sources _ (l+1) C.giant _ _ C.giantCenter
    (nominalInheritedWidth k l) (nominalRemovedWidth k l) (C.cells.center b₀) u _
  · simpa only [reconstructCounterpart_product] using hw.1
  · exact hw.2

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
