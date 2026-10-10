import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorStates
import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def overwritePivot (k j : ℕ) (P : ℤ) (C : State k j) : State k j :=
  fun i => if (schedule k j).IsPivot j i then P else C i

theorem overwritePivot_installWords (k j : ℕ) (P : ℤ) (C : State k j)
    (z : WordSlot k j → ℤ) :
    overwritePivot k j P (installWords k j C z) = installWords k j (overwritePivot k j P C) z := by
  funext i
  by_cases hp : (schedule k j).IsPivot j i
  · have hw : ¬ ((schedule k j).eligible i ∧ (schedule k j).role i = .word) := by
      rintro ⟨_,hw⟩
      rw [hp.2] at hw
      contradiction
    simp only [overwritePivot,ite_eq_left hp,installWords,dite_eq_right hw,mul_one]
  · simp only [overwritePivot,ite_eq_right hp,installWords]

theorem overwritePivot_sourceState (k j : ℕ) (P P0 : ℤ) (h : CopiedState k j) (y : OutsideState k j) :
    overwritePivot k j P (sourceState k j P0 h y) = sourceState k j P h y := by
  funext i
  unfold overwritePivot sourceState childState
  split_ifs <;> rfl

theorem scheduled_constituentPrimePrior_mean (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i))
    (F : ((schedule k j).Constituent width → PrimeUpTo Q) → ℝ) :
    (constituentPrimePrior (schedule k j) width E hE).mean F =
      (outsidePrimePrior (schedule k j) j width E hE).mean (fun y =>
        (pivotPrimePrior k j hj width E hE).mean (fun w =>
          (copiedPrimePrior (schedule k j) j width E hE).mean (fun h =>
            F (scheduledSample k j hj width w h y)))) := by
  have hh := congrArg Complex.re (scheduled_constituentPrimePrior_cmean k j hj width E hE
    (fun x => (F x : ℂ)))
  simpa [FinitePrior.cmean,FinitePrior.mean] using hh

theorem constituentPrimePrior_fixed_pivot_mean (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) (P : ℤ) (F : State k j → ℝ) :
    (constituentPrimePrior (schedule k j) width E hE).mean
      (fun x => F (overwritePivot k j P (constituentSampleState (schedule k j) width x))) =
    (outsidePrimePrior (schedule k j) j width E hE).mean (fun y =>
      (copiedPrimePrior (schedule k j) j width E hE).mean (fun h =>
        F (sourceState k j P (copiedSampleState (schedule k j) j width h)
          (outsideSampleState (schedule k j) j width y)))) := by
  rw [scheduled_constituentPrimePrior_mean k j hj width E hE]
  simp only [constituentSampleState_scheduledSample,overwritePivot_sourceState,FinitePrior.mean_const]

end Ostmann.Characters.Template

end

end OAI
