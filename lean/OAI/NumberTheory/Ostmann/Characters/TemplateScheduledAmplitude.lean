import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceScheduledData
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceTransfer
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryRangeStep

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

section
variable (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E0 : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE0 : ∀i,0<primeShellMass (E0 i))
    (ζ0 : PrimeUnitData (schedule k 0) width Q)
    (χ0 : PrimeCharacterData (schedule k 0) width Q)
    (a0 : PrimeTranslationData (schedule k 0) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X rate m W : ℝ)

def scheduledUnitAmplitude (j : ℕ) : ℂ :=
  unitAmplitude k j width (scheduledUnitData k width ζ0 j)
    (scheduledCharacterData k width χ0 j) (scheduledTranslationData k width a0 j)
    B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask) X (rate*m) W
    (ranges rate m j) (scheduledPrimeShells k width E0 j)
    (scheduledPrimeShells_positive k width E0 hE0 j)

def scheduledUnitDiagonal (j : ℕ) (hj : j<k) : ℝ :=
  unitDiagonal k j hj width (scheduledPrimeShells k width E0 j)
    (scheduledPrimeShells_positive k width E0 hE0 j) (scheduledUnitData k width ζ0 j)
    (scheduledCharacterData k width χ0 j) (scheduledTranslationData k width a0 j)
    B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask) X (rate*m) W
    (ranges rate m j) (R j)

def scheduledPivotFactor (j : ℕ) (hj : j<k) : ℝ :=
  ((width ((schedule k j).role (pivotSlot k j hj).val)).factorial:ℝ)*
    PivotProductFibers.normalization
      (fun i => scheduledPrimeShells k width E0 j ⟨(pivotSlot k j hj).val,i⟩)

@[simp] theorem scheduledUnitAmplitude_zero :
    scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W 0 =
      unitAmplitude k 0 width ζ0 χ0 a0 B V (canonicalHistoryExtra k R)
        (canonicalHistoryMask k leafMask) X (rate*m) W (ranges rate m 0) E0 hE0 := rfl

theorem scheduledUnitAmplitude_succ (j : ℕ) :
    scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W (j+1)=
      unitAmplitude k (j+1) width
        (nextUnitData (schedule k j) j width (scheduledUnitData k width ζ0 j))
        (fun i => scheduledCharacterData k width χ0 j (previousConstituent (schedule k j) j width i))
        (fun i => scheduledTranslationData k width a0 j (previousConstituent (schedule k j) j width i))
        B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask) X (rate*m) W
        (stepHistoryRanges (ranges rate m j) (signedRange (bound rate m (j+1))))
        (nextPrimeShells (schedule k j) j width (scheduledPrimeShells k width E0 j))
        (nextPrimeShells_positive (schedule k j) j width (scheduledPrimeShells k width E0 j)
          (scheduledPrimeShells_positive k width E0 hE0 j)) := by
  rw [stepHistoryRanges_actual]
  rfl

end
end Ostmann.Characters.Template

end

end OAI
