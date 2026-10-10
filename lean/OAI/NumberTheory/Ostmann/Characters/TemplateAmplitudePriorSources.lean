import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorStates

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def previousConstituent (T : Layout) (j : ℕ) (width : Role → ℕ) :
    (T.step j).Constituent width → T.Constituent width := fun i =>
  match nextConstituentEquiv T j width i with
  | .inl (h,_) => copiedConstituentOld T j width h
  | .inr y => outsideConstituentOld T j width y

@[simp] theorem previousConstituent_copied (T : Layout) (j : ℕ) (width : Role → ℕ)
    (h : CopiedConstituent T j width) (b : Bool) :
    previousConstituent T j width ((nextConstituentEquiv T j width).symm (.inl (h,b))) =
      copiedConstituentOld T j width h := by
  simp only [previousConstituent,Equiv.apply_symm_apply]

@[simp] theorem previousConstituent_outside (T : Layout) (j : ℕ) (width : Role → ℕ)
    (y : OutsideConstituent T j width) :
    previousConstituent T j width ((nextConstituentEquiv T j width).symm (.inr y)) =
      outsideConstituentOld T j width y := by
  simp only [previousConstituent,Equiv.apply_symm_apply]

theorem nextPrimeShells_eq_previous (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (i : (T.step j).Constituent width) :
    nextPrimeShells T j width E i = E (previousConstituent T j width i) := by
  unfold nextPrimeShells previousConstituent
  cases h : nextConstituentEquiv T j width i with
  | inl x => rcases x with ⟨h,b⟩; rfl
  | inr y => rfl

def scheduledConstituentOrigin (k : ℕ) (width : Role → ℕ) :
    (j : ℕ) → (schedule k j).Constituent width → (schedule k 0).Constituent width
  | 0 => id
  | j+1 => fun i => scheduledConstituentOrigin k width j
      (previousConstituent (schedule k j) j width i)

def scheduledPrimeShells (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q)) :
    (j : ℕ) → (schedule k j).Constituent width → Finset (PrimeUpTo Q)
  | 0 => E₀
  | j+1 => nextPrimeShells (schedule k j) j width (scheduledPrimeShells k width E₀ j)

@[simp] theorem scheduledPrimeShells_succ (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q)) :
    scheduledPrimeShells k width E₀ (j+1) =
      nextPrimeShells (schedule k j) j width (scheduledPrimeShells k width E₀ j) := rfl

theorem scheduledPrimeShells_eq_origin (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (i : (schedule k j).Constituent width) :
    scheduledPrimeShells k width E₀ j i = E₀ (scheduledConstituentOrigin k width j i) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [scheduledPrimeShells_succ,nextPrimeShells_eq_previous,ih]
    rfl

theorem scheduledPrimeShells_positive (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE₀ : ∀ i, 0 < primeShellMass (E₀ i)) :
    ∀ j i, 0 < primeShellMass (scheduledPrimeShells k width E₀ j i) := by
  intro j i
  rw [scheduledPrimeShells_eq_origin]
  exact hE₀ _

def scheduledPrimePrior (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE₀ : ∀ i, 0 < primeShellMass (E₀ i)) :
    FinitePrior ((schedule k j).Constituent width → PrimeUpTo Q) :=
  constituentPrimePrior (schedule k j) width (scheduledPrimeShells k width E₀ j)
    (scheduledPrimeShells_positive k width E₀ hE₀ j)

theorem scheduledPrimePrior_succ_cmean (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE₀ : ∀ i, 0 < primeShellMass (E₀ i))
    (F : ((schedule k (j+1)).Constituent width → PrimeUpTo Q) → ℂ) :
    (scheduledPrimePrior k (j+1) width E₀ hE₀).cmean F =
      (outsidePrimePrior (schedule k j) j width (scheduledPrimeShells k width E₀ j)
        (scheduledPrimeShells_positive k width E₀ hE₀ j)).cmean (fun y =>
      (copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E₀ j)
        (scheduledPrimeShells_positive k width E₀ hE₀ j)).cmean (fun hL =>
      (copiedPrimePrior (schedule k j) j width (scheduledPrimeShells k width E₀ j)
        (scheduledPrimeShells_positive k width E₀ hE₀ j)).cmean (fun hR =>
        F (nextSample (schedule k j) j width hL hR y)))) :=
  next_constituentPrimePrior_cmean (schedule k j) j width (scheduledPrimeShells k width E₀ j)
    (scheduledPrimeShells_positive k width E₀ hE₀ j) F

end Ostmann.Characters.Template

end

end OAI
