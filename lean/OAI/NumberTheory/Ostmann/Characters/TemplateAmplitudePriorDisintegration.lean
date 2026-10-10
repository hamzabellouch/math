import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem scheduled_constituentPrimePrior_mass (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    (constituentPrimePrior (schedule k j) width E hE).mass (scheduledSample k j hj width w h y) =
      (outsidePrimePrior (schedule k j) j width E hE).mass y *
      (pivotPrimePrior k j hj width E hE).mass w *
      (copiedPrimePrior (schedule k j) j width E hE).mass h := by
  simpa only [constituentPrimePrior,outsidePrimePrior,pivotPrimePrior,copiedPrimePrior,
    characterTuplePrior,scheduledSample,scheduledConstituentInput,constituentInputEquiv_pivot,
    constituentInputEquiv_copied,constituentInputEquiv_outside] using
    productPrior_assembled_mass (scheduledConstituentInput k j hj width)
      (fun i => primeShellPrior (E i) (hE i)) w h y

theorem scheduled_constituentPrimePrior_cmean (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (F : ((schedule k j).Constituent width → PrimeUpTo Q) → ℂ) :
    (constituentPrimePrior (schedule k j) width E hE).cmean F =
      (outsidePrimePrior (schedule k j) j width E hE).cmean (fun y =>
        (pivotPrimePrior k j hj width E hE).cmean (fun w =>
          (copiedPrimePrior (schedule k j) j width E hE).cmean (fun h =>
            F (scheduledSample k j hj width w h y)))) := by
  simpa only [constituentPrimePrior,outsidePrimePrior,pivotPrimePrior,copiedPrimePrior,
    characterTuplePrior,scheduledSample,scheduledConstituentInput,constituentInputEquiv_pivot,
    constituentInputEquiv_copied,constituentInputEquiv_outside] using
    productPrior_split_cmean (scheduledConstituentInput k j hj width)
      (fun i => primeShellPrior (E i) (hE i)) F

@[simp] theorem nextPrimeShells_left (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (i : CopiedConstituent T j width) :
    nextPrimeShells T j width E (nextSampleEquiv T j width (.inl i)) =
      E (copiedConstituentOld T j width i) := rfl

@[simp] theorem nextPrimeShells_right (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (i : CopiedConstituent T j width) :
    nextPrimeShells T j width E (nextSampleEquiv T j width (.inr (.inl i))) =
      E (copiedConstituentOld T j width i) := rfl

@[simp] theorem nextPrimeShells_outside (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (i : OutsideConstituent T j width) :
    nextPrimeShells T j width E (nextSampleEquiv T j width (.inr (.inr i))) =
      E (outsideConstituentOld T j width i) := rfl

theorem next_constituentPrimePrior_mass (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (hL hR : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) :
    (constituentPrimePrior (T.step j) width (nextPrimeShells T j width E)
      (nextPrimeShells_positive T j width E hE)).mass (nextSample T j width hL hR y) =
      (outsidePrimePrior T j width E hE).mass y *
      (copiedPrimePrior T j width E hE).mass hL * (copiedPrimePrior T j width E hE).mass hR := by
  simpa only [constituentPrimePrior,outsidePrimePrior,copiedPrimePrior,nextSample,
    nextPrimeShells_left,nextPrimeShells_right,nextPrimeShells_outside] using
    productPrior_assembled_mass (nextSampleEquiv T j width)
      (fun i => primeShellPrior (nextPrimeShells T j width E i)
        (nextPrimeShells_positive T j width E hE i)) hL hR y

theorem next_constituentPrimePrior_cmean (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (F : ((T.step j).Constituent width → PrimeUpTo Q) → ℂ) :
    (constituentPrimePrior (T.step j) width (nextPrimeShells T j width E)
      (nextPrimeShells_positive T j width E hE)).cmean F =
      (outsidePrimePrior T j width E hE).cmean (fun y =>
        (copiedPrimePrior T j width E hE).cmean (fun hL =>
          (copiedPrimePrior T j width E hE).cmean (fun hR =>
            F (nextSample T j width hL hR y)))) := by
  simpa only [constituentPrimePrior,outsidePrimePrior,copiedPrimePrior,nextSample,
    nextPrimeShells_left,nextPrimeShells_right,nextPrimeShells_outside] using
    productPrior_split_cmean (nextSampleEquiv T j width)
      (fun i => primeShellPrior (nextPrimeShells T j width E i)
        (nextPrimeShells_positive T j width E hE i)) F

end Ostmann.Characters.Template

end

end OAI
