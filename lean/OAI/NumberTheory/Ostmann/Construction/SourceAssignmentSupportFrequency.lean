import OAI.NumberTheory.Ostmann.Construction.OffDiagonalReindex
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportCells
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportCenters

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Conclusion
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k L/2)

theorem pivotPairWeight_frequency_cutoff (C : InitialSourceChoice d Bs BD Bz k L E)
    (s l : ℕ) (hl : l<k)
    (hL : 20+10*(k:ℝ)+Real.log 2≤Real.sqrt (bulkSize k L))
    (X : ℝ) (outside : List ℕ)
    (u : SourceAssignment C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l)))
    (x y : RemainingSample C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant)
    (v w : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
    (hu : (assignmentPrior C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l))).mass u≠0)
    (hx : (remainingPrior C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant).mass x≠0)
    (hy : (remainingPrior C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant).mass y≠0)
    (p : ℕ) (hp : p∈integerPivotCell C.giantCenter) (r : ℤ)
    (heq : joinedNumerator C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant x y v.val w.val =
      r*((assignedSlots C.sources (Template.extracted (l+1)
        (Template.current (Template.initial (2*b₀) k) l)) u).map SmallSlot.value).prod*(p:ℤ))
    (hF : pivotPairWeight d C.favorable C.sources (Template.initial (2*b₀) k)
      (frequencyBound Bs BD Bz k L) C.giant X C.giantCenter
      (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin) outside l u x y v w p≠0) :
    r.natAbs≤frequencyBound Bs BD Bz k L (l+1) := by
  have hf := pivotPairWeight_nonzero d C.favorable C.sources (Template.initial (2*b₀) k)
    (frequencyBound Bs BD Bz k L) C.giant X C.giantCenter
    (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin) outside l u x y v w p hF
  have hxs := C.remaining_log_support (l+1) l x hx
  have hys := C.remaining_log_support (l+1) l y hy
  refine remainingState_offDiagonal_frequency_cutoff C.sources b₀ s k l hl
    Bs BD Bz L X C.giantCenter C.bulkBin C.spectatorBin
    (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin) hL
    C.giant (residueTransform d) outside p (Finset.mem_Ioc.mp hp).1 u
    (fun i => if i then y else x) (fun i => if i then w.val else v.val)
    (C.cells.center b₀) (C.top_frequency_center_error b₀)
    (C.type_frequency_center_error b₀) ?_ (C.extracted_log_support (l+1) l u hu) ?_ hf.1 ?_ r ?_
  · intro i
    cases i
    · exact hxs.1
    · exact hys.1
  · intro i
    cases i
    · exact hxs.2
    · exact hys.2
  · intro i
    cases i
    · exact (mul_ne_zero_iff.mp hf.2.1).2
    · exact (mul_ne_zero_iff.mp hf.2.2).2
  · simpa only [joinedNumerator,Arithmetic.reversalNumerator,Bool.false_eq_true,
      ite_false,ite_true] using heq.symm

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
