import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem constituentSampleState_prime_factor_gt (T : Layout) (width : Role → ℕ) {Q V : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (hV : ∀ i p, p ∈ E i → V < p.val) (x : T.Constituent width → PrimeUpTo Q)
    (hx : (constituentPrimePrior T width E hE).mass x ≠ 0)
    (i : T.Slot) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ (constituentSampleState T width x i).natAbs) : V < q := by
  apply prime_factor_sampleProduct_gt (fun a => x ⟨i,a⟩) _ hq hd
  intro a
  exact primeProductPrior_prime_gt E hE hV x hx ⟨i,a⟩

theorem copiedSampleState_prime_factor_gt (T : Layout) (j : ℕ) (width : Role → ℕ) {Q V : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (hV : ∀ i p, p ∈ E i → V < p.val) (x : CopiedConstituent T j width → PrimeUpTo Q)
    (hx : (copiedPrimePrior T j width E hE).mass x ≠ 0)
    (i : {i:T.Slot // T.IsCopied j i}) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ (copiedSampleState T j width x i).natAbs) : V < q := by
  apply prime_factor_sampleProduct_gt (fun a => x ⟨i,a⟩) _ hq hd
  intro a
  exact primeProductPrior_prime_gt (fun i => E (copiedConstituentOld T j width i))
    (fun i => hE (copiedConstituentOld T j width i))
    (fun i p hp => hV (copiedConstituentOld T j width i) p hp) x hx ⟨i,a⟩

theorem outsideSampleState_prime_factor_gt (T : Layout) (j : ℕ) (width : Role → ℕ) {Q V : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (hV : ∀ i p, p ∈ E i → V < p.val) (x : OutsideConstituent T j width → PrimeUpTo Q)
    (hx : (outsidePrimePrior T j width E hE).mass x ≠ 0)
    (i : {i:T.Slot // T.IsOutside j i}) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ (outsideSampleState T j width x i).natAbs) : V < q := by
  apply prime_factor_sampleProduct_gt (fun a => x ⟨i,a⟩) _ hq hd
  intro a
  exact primeProductPrior_prime_gt (fun i => E (outsideConstituentOld T j width i))
    (fun i => hE (outsideConstituentOld T j width i))
    (fun i p hp => hV (outsideConstituentOld T j width i) p hp) x hx ⟨i,a⟩

theorem pairedSampleState_prime_factor_gt (k j : ℕ) (width : Role → ℕ) {Q V : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (hV : ∀ i p, p ∈ E i → V < p.val)
    (hL hR : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hLmass : (copiedPrimePrior (schedule k j) j width E hE).mass hL ≠ 0)
    (hRmass : (copiedPrimePrior (schedule k j) j width E hE).mass hR ≠ 0)
    (hymass : (outsidePrimePrior (schedule k j) j width E hE).mass y ≠ 0)
    (s : ℤ) (hs : s.natAbs ≤ V) (i : (schedule k (j+1)).Slot) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ (pairedState k j (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y) i).natAbs) : s.natAbs < q := by
  apply hs.trans_lt
  rcases i with ⟨i,b⟩ | i
  · cases b
    · exact copiedSampleState_prime_factor_gt _ j width E hE hV hR hRmass i q hq hd
    · exact copiedSampleState_prime_factor_gt _ j width E hE hV hL hLmass i q hq hd
  · exact outsideSampleState_prime_factor_gt _ j width E hE hV y hymass i q hq hd

theorem scheduledPrimeShells_prime_gt (k j : ℕ) (width : Role → ℕ) {Q V : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hV : ∀ i p, p ∈ E₀ i → V < p.val) :
    ∀ i p, p ∈ scheduledPrimeShells k width E₀ j i → V < p.val := by
  intro i p hp
  rw [scheduledPrimeShells_eq_origin] at hp
  exact hV _ p hp

theorem scheduledPrimePrior_prime_factor_gt (k j : ℕ) (width : Role → ℕ) {Q V : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hE₀ : ∀ i, 0 < primeShellMass (E₀ i)) (hV : ∀ i p, p ∈ E₀ i → V < p.val)
    (x : (schedule k j).Constituent width → PrimeUpTo Q)
    (hx : (scheduledPrimePrior k j width E₀ hE₀).mass x ≠ 0)
    (s : ℤ) (hs : s.natAbs ≤ V) (i : (schedule k j).Slot) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ (constituentSampleState (schedule k j) width x i).natAbs) : s.natAbs < q :=
  hs.trans_lt (constituentSampleState_prime_factor_gt _ width _
    (scheduledPrimeShells_positive k width E₀ hE₀ j)
    (scheduledPrimeShells_prime_gt k j width E₀ hV) x hx i q hq hd)

end Ostmann.Characters.Template

end

end OAI
