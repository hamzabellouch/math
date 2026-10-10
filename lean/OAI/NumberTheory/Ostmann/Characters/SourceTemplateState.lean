import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePriors
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceWord HigherBiasSourceRoleBounds
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sourceLeafMask (k : ℕ) (J : ℤ) (_s : ℤ) (x : State k 0) : Prop :=
  ⌊Real.log (x (.word,true) : ℝ)⌋ = J ∧ ⌊Real.log (x (.word,false) : ℝ)⌋ = J

theorem sourceSample_mask_state {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ) (J s : ℤ)
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    characterDoubleMask (sourceHalfMask J) w =
      if sourceLeafMask k J s (constituentSampleState (schedule k 0) (sourceWidth cfg m)
        (sourceSample cfg m w)) then 1 else 0 := by
  rw [sourceSample_mask cfg m J w, templateWordMask_eq_state_bin cfg m J _ true,
    templateWordMask_eq_state_bin cfg m J _ false]
  unfold sourceLeafMask
  split_ifs <;> simp_all

theorem constituentSampleState_period (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) :
    (∏ i : T.Slot, constituentSampleState T width x i) =
      ∏ i : T.Constituent width, ((x i).val : ℤ) :=
  (Fintype.prod_sigma (fun i : T.Constituent width => ((x i).val : ℤ))).symm

theorem sourceSample_period {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    period k 0 (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w)) =
      (characterTupleProduct w : ℤ) := by
  unfold period
  rw [constituentSampleState_period]
  change (∏ i, ((w (sourceIndexEquiv cfg m i)).val : ℤ)) = _
  rw [(sourceIndexEquiv cfg m).prod_comp (fun i => ((w i).val : ℤ))]
  simp only [characterTupleProduct, Nat.cast_prod]

theorem sourceSample_primeSupport {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    samplePrimeSupport (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w) ↔
      Pairwise (fun i j => (w i).val.Coprime (w j).val) := by
  constructor
  · intro h i j hij
    have hh := h (show (sourceIndexEquiv cfg m).symm i ≠ (sourceIndexEquiv cfg m).symm j from
      fun he => hij ((sourceIndexEquiv cfg m).symm.injective he))
    simpa only [sourceSample, Equiv.apply_symm_apply] using hh
  · intro h i j hij
    exact h (fun he => hij ((sourceIndexEquiv cfg m).injective he))

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
