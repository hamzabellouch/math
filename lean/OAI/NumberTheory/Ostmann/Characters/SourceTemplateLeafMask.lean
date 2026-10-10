import OAI.NumberTheory.Ostmann.Characters.SourceTemplateState
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceCanonical

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HigherBiasSourceWord
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sourceRangeLeafMask (k : ℕ) (J : ℤ) (X Δ W : ℝ) (s : ℤ) (x : State k 0) : Prop :=
  sourceLeafMask k J s x ∧
    X*Real.exp (Δ-W) ≤ (period k 0 x:ℝ) ∧
    (period k 0 x:ℝ) ≤ X*Real.exp (Δ+W)

theorem sourceRangeLeafMask_upper {k J X Δ W s x}
    (h : sourceRangeLeafMask k J X Δ W s x) :
    (period k 0 x:ℝ) ≤ X*Real.exp (Δ+W) := h.2.2

theorem sourceRangeLeafMask_log_lower {k J X Δ W s x} (hX : 0 < X)
    (h : sourceRangeLeafMask k J X Δ W s x) :
    Real.log X+Δ-W ≤ Real.log (period k 0 x:ℝ) := by
  have hp : 0 < X*Real.exp (Δ-W) := mul_pos hX (Real.exp_pos _)
  have hh := Real.log_le_log hp h.2.1
  rw [Real.log_mul hX.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  linarith

theorem sourceSample_range_mask {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (J s : ℤ) (X Δ W : ℝ)
    (w : Fin (sourceHalfSize cfg m+sourceHalfSize cfg m) → PrimeUpTo Q)
    (hwindow : characterDoubleMask (sourceHalfMask J) w ≠ 0 →
      X*Real.exp (Δ-W) ≤ (characterTupleProduct w:ℝ) ∧
      (characterTupleProduct w:ℝ) ≤ X*Real.exp (Δ+W)) :
    characterDoubleMask (sourceHalfMask J) w =
      if sourceRangeLeafMask k J X Δ W s
        (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w))
      then 1 else 0 := by
  have hb := sourceSample_mask_state cfg m J s w
  by_cases h : sourceLeafMask k J s
      (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w))
  · rw [ite_eq_left h] at hb
    have hp := hwindow (by rw [hb]; norm_num)
    have hr : sourceRangeLeafMask k J X Δ W s
        (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w)) := by
      refine ⟨h,?_⟩
      rw [sourceSample_period cfg m w]
      simpa only [Int.cast_natCast] using hp
    rw [ite_eq_left hr,hb]
  · have hr : ¬sourceRangeLeafMask k J X Δ W s
        (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w)) :=
      fun hh => h hh.1
    rw [ite_eq_right hr]
    simpa only [ite_eq_right h] using hb

theorem sourceSample_primeSupport_iff_injective {k Q : ℕ} (cfg : SourceConfiguration k)
    (m : ℕ) (w : Fin (sourceHalfSize cfg m+sourceHalfSize cfg m) → PrimeUpTo Q) :
    samplePrimeSupport (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w) ↔
      Function.Injective w := by
  rw [sourceSample_primeSupport]
  constructor
  · intro h i j he
    by_contra hij
    have hc := h hij
    change (w i).val.Coprime (w j).val at hc
    rw [he] at hc
    exact (primeUpTo_prime (w j)).ne_one ((Nat.coprime_self _).mp hc)
  · intro h i j hij
    apply (Nat.coprime_primes (primeUpTo_prime (w i)) (primeUpTo_prime (w j))).mpr
    exact fun he => hij (h (Subtype.ext he))

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
