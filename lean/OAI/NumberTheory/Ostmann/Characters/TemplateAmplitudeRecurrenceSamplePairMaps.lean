import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryTransfer

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def pairedOutputSample (k j:ℕ) (width:Role→ℕ) {Q:ℕ}
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q) :
    UnaryOutputIndex k j width→PrimeUpTo Q :=
  Sum.elim (fun ib => if ib.2 then hL ib.1 else hR ib.1) y

theorem nextSample_output (k j:ℕ) (width:Role→ℕ) {Q:ℕ}
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (i:UnaryOutputIndex k j width) :
    nextSample (schedule k j) j width hL hR y
      ((nextConstituentEquiv (schedule k j) j width).symm i)=
      pairedOutputSample k j width hL hR y i := by
  change Sum.elim hL (Sum.elim hR y)
    ((copyPairInputEquiv _ _).symm
      (nextConstituentEquiv (schedule k j) j width
        ((nextConstituentEquiv (schedule k j) j width).symm i)))=_
  rw [Equiv.apply_symm_apply]
  rcases i with ⟨i,_ | _⟩ | i <;> rfl

theorem nextSample_output_apply (k j:ℕ) (width:Role→ℕ) {Q:ℕ}
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (i:(schedule k (j+1)).Constituent width) :
    nextSample (schedule k j) j width hL hR y i=
      pairedOutputSample k j width hL hR y (nextConstituentEquiv (schedule k j) j width i) := by
  simpa only [Equiv.symm_apply_apply] using nextSample_output k j width hL hR y
    (nextConstituentEquiv (schedule k j) j width i)

end Ostmann.Characters.Template

end

end OAI
