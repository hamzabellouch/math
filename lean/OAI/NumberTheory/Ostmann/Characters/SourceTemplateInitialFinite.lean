import OAI.NumberTheory.Ostmann.Characters.CharacterPhaseBounds
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateLeafMask
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateTruncation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open scoped BigOperators FourierTransform
attribute [local instance] Classical.propDecidable

theorem source_unitHistoryPhase_zero {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (χ : Fin (sourceHalfSize cfg m) → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin (sourceHalfSize cfg m) → (q:ℕ) → ZMod q)
    (ζ : Fin (sourceHalfSize cfg m) → ℕ → ℂ)
    (w : Fin (sourceHalfSize cfg m+sourceHalfSize cfg m) → PrimeUpTo Q) :
    unitHistoryPhase k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
      (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
      (sourceSample cfg m w) 0 PUnit.unit = 0 := by
  let : Nonempty (Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)) :=
    ⟨⟨0,by simp only [sourceHalfSize]; omega⟩⟩
  let : ∀i,Fact (w i).val.Prime := fun i=>⟨primeUpTo_prime (w i)⟩
  rw [sourceSample_unitHistoryPhase cfg m χ a ζ w 0 PUnit.unit,initialPhase_zero,mul_zero]

theorem characterTupleFourier_eq_finite_leaf_sum {k Q : ℕ} (cfg : SourceConfiguration k)
    (m : ℕ) (χ : Fin (sourceHalfSize cfg m) → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin (sourceHalfSize cfg m) → (q:ℕ) → ZMod q)
    (ζ : Fin (sourceHalfSize cfg m) → ℕ → ℂ) (X Δ W : ℝ) (hX : 0 < X)
    (w : Fin (sourceHalfSize cfg m+sourceHalfSize cfg m) → PrimeUpTo Q)
    (hlog : Real.log X+Δ-W ≤ Real.log (characterTupleProduct w:ℝ))
    (V₀ : ℕ) (hPV : (characterTupleProduct w:ℝ) ≤ 4*X*V₀) :
    characterTupleFourier (characterDoubleChar χ) (characterDoubleCenter a)
      (characterDoublePhase ζ) X w =
    ∑s∈signedRange V₀,leafWeight k X Δ W s
      (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w))*
      unitHistoryPhase k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
        (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
        (sourceSample cfg m w) s PUnit.unit := by
  rw [characterTupleFourier_eq_leaf_sum cfg m χ a ζ X Δ W w hlog]
  apply leaf_phase_tsum_eq_sum X Δ W hX _ V₀
  · rw [sourceSample_period cfg m w]
    simpa only [Int.cast_natCast] using hPV
  · exact source_unitHistoryPhase_zero cfg m χ a ζ w

theorem retained_leaf_phase_eq {k : ℕ}
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X Δ W : ℝ) (s : ℤ) (x : State k 0)
    (f : ℂ) (hf : f ≠ 0 → CurrentAtomSupport k 0 s x) :
    retainedHistoryWeight k B V (canonicalHistoryExtra k R)
      (canonicalHistoryMask k leafMask) X Δ W 0 s x PUnit.unit * f =
      (if leafMask s x then leafWeight k X Δ W s x else 0)*f := by
  by_cases hz : f = 0
  · simp only [hz,mul_zero]
  · have hc := hf hz
    simp only [retainedHistoryWeight,TransferSupport,canonicalHistoryExtra,hc,
      and_self,ite_true,weight,canonicalHistoryMask]
    rfl

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
