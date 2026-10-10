import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSize
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem frequency_ne_zero_mod_of_natAbs_lt {p V : ℕ} {f : ℤ}
    (hf : f ≠ 0) (hV : f.natAbs ≤ V) (hp : V < p) : (f : ZMod p) ≠ 0 := by
  intro hz
  have hdZ : (p:ℤ) ∣ f := (ZMod.intCast_zmod_eq_zero_iff_dvd f p).mp hz
  have hd : p ∣ f.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdZ
  exact (not_le_of_gt (hV.trans_lt hp)) (Nat.le_of_dvd (Int.natAbs_pos.mpr hf) hd)

theorem historyFrequencyUnits_of_prime_gt_cutoff {p V j : ℕ}
    (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f ∈ S path → f ≠ 0 ∧ f.natAbs ≤ V)
    (hp : V < p) (path : List Bool)
    (z : HistoryFrequencyLabels.SupportedHistory S j path) :
    HistoryFrequencyUnits p j z.val.1 z.val.2 := by
  apply historyFrequencyUnits_of_range S _ z.property
  intro a f hf
  exact frequency_ne_zero_mod_of_natAbs_lt (hS a f hf).1 (hS a f hf).2 hp

theorem primeProductPrior_historyFrequencyUnits {I : Type*} [Fintype I] {Q V j : ℕ}
    (E : I → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (hV : ∀ i p, p ∈ E i → V < p.val) (x : I → PrimeUpTo Q)
    (hx : (productPrior (fun i => primeShellPrior (E i) (hE i))).mass x ≠ 0)
    (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f ∈ S path → f ≠ 0 ∧ f.natAbs ≤ V)
    (path : List Bool) (z : HistoryFrequencyLabels.SupportedHistory S j path) (i : I) :
    HistoryFrequencyUnits (x i).val j z.val.1 z.val.2 :=
  historyFrequencyUnits_of_prime_gt_cutoff S hS
    (primeProductPrior_prime_gt E hE hV x hx i) path z

theorem constituentPrimePrior_historyFrequencyUnits (T : Layout) (width : Role → ℕ)
    {Q V j : ℕ} (E : T.Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (hV : ∀ i p, p ∈ E i → V < p.val)
    (x : T.Constituent width → PrimeUpTo Q)
    (hx : (constituentPrimePrior T width E hE).mass x ≠ 0)
    (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f ∈ S path → f ≠ 0 ∧ f.natAbs ≤ V)
    (path : List Bool) (z : HistoryFrequencyLabels.SupportedHistory S j path)
    (i : T.Constituent width) : HistoryFrequencyUnits (x i).val j z.val.1 z.val.2 :=
  primeProductPrior_historyFrequencyUnits E hE hV x hx S hS path z i

theorem copiedPrimePrior_historyFrequencyUnits (T : Layout) (n : ℕ) (width : Role → ℕ)
    {Q V j : ℕ} (E : T.Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (hV : ∀ i p, p ∈ E i → V < p.val)
    (x : CopiedConstituent T n width → PrimeUpTo Q)
    (hx : (copiedPrimePrior T n width E hE).mass x ≠ 0)
    (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f ∈ S path → f ≠ 0 ∧ f.natAbs ≤ V)
    (path : List Bool) (z : HistoryFrequencyLabels.SupportedHistory S j path)
    (i : CopiedConstituent T n width) : HistoryFrequencyUnits (x i).val j z.val.1 z.val.2 :=
  primeProductPrior_historyFrequencyUnits (fun i => E (copiedConstituentOld T n width i))
    (fun i => hE (copiedConstituentOld T n width i))
    (fun i p hp => hV (copiedConstituentOld T n width i) p hp) x hx S hS path z i

theorem outsidePrimePrior_historyFrequencyUnits (T : Layout) (n : ℕ) (width : Role → ℕ)
    {Q V j : ℕ} (E : T.Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (hV : ∀ i p, p ∈ E i → V < p.val)
    (x : OutsideConstituent T n width → PrimeUpTo Q)
    (hx : (outsidePrimePrior T n width E hE).mass x ≠ 0)
    (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f ∈ S path → f ≠ 0 ∧ f.natAbs ≤ V)
    (path : List Bool) (z : HistoryFrequencyLabels.SupportedHistory S j path)
    (i : OutsideConstituent T n width) : HistoryFrequencyUnits (x i).val j z.val.1 z.val.2 :=
  primeProductPrior_historyFrequencyUnits (fun i => E (outsideConstituentOld T n width i))
    (fun i => hE (outsideConstituentOld T n width i))
    (fun i p hp => hV (outsideConstituentOld T n width i) p hp) x hx S hS path z i

end Ostmann.Characters.Template

end

end OAI
