import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSourceFactorDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsCopied

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

theorem retained_source_copied_log_target {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (J : ℤ) (gaps : ℕ → ℝ) (logX c : ℝ)
    (hj : j < k) (hc : 0 < c)
    (hlist : ∀ a, |((cfg.2 a).sum:ℝ)-configurationTarget logX J gaps cfg a| ≤ 6/c)
    (hlen : ∀ a, ((cfg.2 a).length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k)))
    (hE : ∀ i,0 < primeShellMass (scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j i))
    (h : CopiedConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hmass : (copiedPrimePrior (schedule k j) j (sourceWidth cfg m)
      (scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j) hE).mass h ≠ 0)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (X δ₀ W : ℝ) (P s : ℤ) (y : OutsideState k j) (t : HistoryReconstruction.Tree j)
    (hret : retainedHistoryWeight k B V extra
      (canonicalHistoryMask k (sourceRangeLeafMask k J X δ₀ W)) X δ₀ W j s
      (sourceState k j P (copiedSampleState (schedule k j) j (sourceWidth cfg m) h) y) t ≠ 0) :
    |Real.log ((∏ i,(h i).val:ℕ):ℝ)-(sourcePivotTarget cfg J gaps j+gaps (j+1))| ≤
      sourceCopiedWidth k c := by
  have hh := source_copied_log_target cfg m j bulk top E J gaps logX c hj hc hlist hlen h
    (fun a => primeProductPrior_mem_of_mass_ne_zero
      (fun a => scheduledPrimeShells k (sourceWidth cfg m)
        (configurationPrimeShells cfg m bulk top E) j (copiedConstituentOld _ _ _ a))
      (fun a => hE (copiedConstituentOld _ _ _ a)) h hmass a)
    (fun i => retainedHistoryWeight_source_copied_word_bin hret i)
  rw [prod_copiedSampleState] at hh
  simpa only [Int.cast_natCast] using hh

theorem retained_source_copied_window {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (J : ℤ) (gaps : ℕ → ℝ) (logX c : ℝ)
    (hj : j < k) (hc : 0 < c)
    (hlist : ∀ a, |((cfg.2 a).sum:ℝ)-configurationTarget logX J gaps cfg a| ≤ 6/c)
    (hlen : ∀ a, ((cfg.2 a).length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k)))
    (hE : ∀ i,0 < primeShellMass (scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j i))
    (h : CopiedConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hmass : (copiedPrimePrior (schedule k j) j (sourceWidth cfg m)
      (scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j) hE).mass h ≠ 0)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (X δ₀ W : ℝ) (P s : ℤ) (y : OutsideState k j) (t : HistoryReconstruction.Tree j)
    (hret : retainedHistoryWeight k B V extra
      (canonicalHistoryMask k (sourceRangeLeafMask k J X δ₀ W)) X δ₀ W j s
      (sourceState k j P (copiedSampleState (schedule k j) j (sourceWidth cfg m) h) y) t ≠ 0) :
    Real.exp (sourcePivotTarget cfg J gaps j+gaps (j+1)-sourceCopiedWidth k c) ≤
      ((∏ i,(h i).val:ℕ):ℝ) ∧
    ((∏ i,(h i).val:ℕ):ℝ) ≤
      Real.exp (sourcePivotTarget cfg J gaps j+gaps (j+1)+sourceCopiedWidth k c) := by
  have hh := abs_le.mp (retained_source_copied_log_target cfg m j bulk top E J gaps logX c
    hj hc hlist hlen hE h hmass B V extra X δ₀ W P s y t hret)
  have hp : 0 < ((∏ i,(h i).val:ℕ):ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (primeUpTo_prime (h i)).pos)
  constructor
  · have he := Real.exp_le_exp.mpr (show sourcePivotTarget cfg J gaps j+gaps (j+1)-sourceCopiedWidth k c ≤ Real.log ((∏ i,(h i).val:ℕ):ℝ) by linarith [hh.1])
    simpa only [Real.exp_log hp] using he
  · have he := Real.exp_le_exp.mpr (show Real.log ((∏ i,(h i).val:ℕ):ℝ) ≤ sourcePivotTarget cfg J gaps j+gaps (j+1)+sourceCopiedWidth k c by linarith [hh.2])
    simpa only [Real.exp_log hp] using he

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
