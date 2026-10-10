import OAI.NumberTheory.Ostmann.Characters.SourceTemplateInitialFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem source_integrand_of_phase_support {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (χ : Fin (sourceHalfSize cfg m) → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin (sourceHalfSize cfg m) → (q:ℕ) → ZMod q)
    (ζ : Fin (sourceHalfSize cfg m) → ℕ → ℂ)
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (J : ℤ) (X Δ W : ℝ) (hX : 0 < X) (V₀ : ℕ)
    (hcut : Real.exp (Δ+W) ≤ 4*(V₀:ℝ))
    (S : List Bool → Finset ℤ) (hS : S [] = signedRange V₀)
    (w : Fin (sourceHalfSize cfg m+sourceHalfSize cfg m) → PrimeUpTo Q)
    (hwindow : characterDoubleMask (sourceHalfMask J) w ≠ 0 →
      X*Real.exp (Δ-W) ≤ (characterTupleProduct w:ℝ) ∧
      (characterTupleProduct w:ℝ) ≤ X*Real.exp (Δ+W))
    (hphase : Function.Injective w → ∀ s,
      unitHistoryPhase k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
        (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
        (sourceSample cfg m w) s PUnit.unit ≠ 0 →
      CurrentAtomSupport k 0 s (constituentSampleState (schedule k 0) (sourceWidth cfg m)
        (sourceSample cfg m w))) :
    unitAmplitudeIntegrand k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
      (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a) B V
      (canonicalHistoryExtra k R) (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W))
      X Δ W S (sourceSample cfg m w) =
    if Function.Injective w then (characterDoubleMask (sourceHalfMask J) w:ℂ)*
      characterTupleFourier (characterDoubleChar χ) (characterDoubleCenter a)
        (characterDoublePhase ζ) X w else 0 := by
  rw [unitAmplitudeIntegrand_eq,sourceSample_primeSupport_iff_injective cfg m w]
  by_cases hw : Function.Injective w
  · rw [ite_eq_left hw,ite_eq_left hw]
    rw [sum_supportedHistory_zero S (fun s t =>
      retainedHistoryWeight k B V (canonicalHistoryExtra k R)
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W)) X Δ W 0 s
        (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w)) t *
      unitHistoryPhase k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
        (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
        (sourceSample cfg m w) s t),hS]
    have he (s:ℤ) :
        retainedHistoryWeight k B V (canonicalHistoryExtra k R)
          (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W)) X Δ W 0 s
          (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w))
          PUnit.unit *
        unitHistoryPhase k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
          (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
          (sourceSample cfg m w) s PUnit.unit =
        (characterDoubleMask (sourceHalfMask J) w:ℂ)*
          (leafWeight k X Δ W s (constituentSampleState (schedule k 0) (sourceWidth cfg m)
            (sourceSample cfg m w))*
          unitHistoryPhase k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
            (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
            (sourceSample cfg m w) s PUnit.unit) := by
      rw [retained_leaf_phase_eq B V R _ X Δ W s _ _ (hphase hw s),
        sourceSample_range_mask cfg m J s X Δ W w hwindow]
      split_ifs <;> simp
    simp_rw [he]
    rw [← Finset.mul_sum]
    by_cases hm : characterDoubleMask (sourceHalfMask J) w = 0
    · simp only [hm,Complex.ofReal_zero,zero_mul]
    · have hr : sourceRangeLeafMask k J X Δ W 0
          (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w)) := by
        have hb := sourceSample_range_mask cfg m J 0 X Δ W w hwindow
        by_contra hn
        rw [ite_eq_right hn] at hb
        exact hm hb
      have hlog := sourceRangeLeafMask_log_lower hX hr
      rw [sourceSample_period cfg m w] at hlog
      simp only [Int.cast_natCast] at hlog
      have hPV : (characterTupleProduct w:ℝ) ≤ 4*X*V₀ :=
        (hwindow hm).2.trans (by nlinarith [mul_le_mul_of_nonneg_left hcut hX.le])
      rw [characterTupleFourier_eq_finite_leaf_sum cfg m χ a ζ X Δ W hX w hlog V₀ hPV]
  · simp only [ite_eq_right hw]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
