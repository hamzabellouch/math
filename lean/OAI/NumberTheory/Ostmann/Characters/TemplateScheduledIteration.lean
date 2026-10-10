import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeIterationScales
import OAI.NumberTheory.Ostmann.Characters.TemplateScheduledBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

theorem scheduledUnitAmplitude_lower (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E0 : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE0 : ∀i,0<primeShellMass (E0 i))
    (ζ0 : PrimeUnitData (schedule k 0) width Q) (hζ0 : ∀i p,‖ζ0 i p‖=1)
    (χ0 : PrimeCharacterData (schedule k 0) width Q) (hχ0 : ∀i p,p∈E0 i→χ0 i p≠1)
    (a0 : PrimeTranslationData (schedule k 0) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X rate m W : ℝ)
    (hrate : 0 ≤ rate) (hm : 1 ≤ m)
    (bounds : ∀j (hj:j<k),
      ScheduledTransferBounds k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j hj)
    (B0 B1 : ℝ) (d : ℕ → ℝ) (hd : ∀j,0≤d j)
    (hbudget : (∑j∈Finset.range k,(d j+Real.log 2))≤(B1-B0)*m)
    (hinitial : Real.exp (-B0*m)≤
      ‖scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W 0‖)
    (hfactor : ∀j (hj:j<k),scheduledPivotFactor k width E0 j hj≤Real.exp (d j))
    (hdiag : ∀j (hj:j<k),
      scheduledUnitDiagonal k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j hj≤
        (1/2:ℝ)*Real.exp (-d j)*Real.exp (-2*B1*(2:ℝ)^j*m)) :
    ∀j≤k,Real.exp (-B1*(2:ℝ)^j*m)≤
      ‖scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j‖ := by
  let η : ℕ → ℝ := fun j =>
    ‖scheduledUnitAmplitude k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j‖
  let D : ℕ → ℝ := fun j => if hj:j<k then
    scheduledUnitDiagonal k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j hj else 0
  let F : ℕ → ℝ := fun j => if hj:j<k then scheduledPivotFactor k width E0 j hj else 1
  refine TemplateAmplitudeIteration.amplitude_budget_of_factor k B0 B1 m η d D F hd
    (fun j => norm_nonneg _) ?_ hbudget hinitial ?_ ?_ ?_
  · intro j
    dsimp only [D]
    split
    · exact scheduledUnitDiagonal_nonneg k width E0 hE0 ζ0 χ0 a0 B V R leafMask X rate m W j _
    · exact le_rfl
  · intro j hj
    simpa only [F,hj,dite_true] using hfactor j hj
  · intro j hj
    simpa only [η,D,F,hj,dite_true] using
      scheduledUnitAmplitude_transfer_of_bounds k width E0 hE0 ζ0 χ0 a0 B V R leafMask
        X rate m W j hj hζ0 hχ0 hrate hm (bounds j hj)
  · intro j hj
    simpa only [D,hj,dite_true] using hdiag j hj

end Ostmann.Characters.Template

end

end OAI
