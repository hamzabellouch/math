import OAI.NumberTheory.Ostmann.Arithmetic.BulkFrequencyFactor
import OAI.NumberTheory.Ostmann.Construction.PrimeGridResidueLift

namespace OAI

/-! # The frequency factor evaluated on the actual bulk residue representative -/

namespace Ostmann
open scoped Classical

/-- Once the nonbulk coordinates have been fixed, the frequency factor is
a function of the frequency-unit array alone. The representative does not
alter any compensation denominator. -/
theorem movingFrequencyCore_bulk_residues {σ J : Type*}
    (value : σ → ℕ) (e : J ↪ σ) (r : ℕ) [NeZero r]
    (a : J → (ZMod r)ˣ) (ha : ∀ j, (value (e j) : ZMod r) = (a j : ZMod r))
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hT : ∀ b j, (T b).CompensationAbsent (e j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (XL XR : ℤ) :
    movingFrequencyCore value F E T R XL XR =
      movingFrequencyCore (Function.extend e (fun j => (a j).val.val) value) F E T R XL XR := by
  let w := Function.extend e (fun j => (a j).val.val) value
  have hcomp (b : Bool) : (T b).CompensationAgreement value w := by
    apply (T b).compensationAgreement_of_eq_off value w (Set.range e)
    · rintro i ⟨j, rfl⟩
      exact hT b j
    · intro i hi
      exact (Function.extend_apply' _ value i hi).symm
  have hv (i : σ) : (value i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (n + 1)] := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      have he : (value (e j) : ℤ) ≡ ((a j).val.val : ℤ) [ZMOD (r : ℤ)] := by
        apply (ZMod.intCast_eq_intCast_iff _ _ r).mp
        simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using ha j
      simpa only [w, e.injective.extend_apply] using he.of_dvd hr
    · rw [show w i = value i from Function.extend_apply' _ value i hi]
  exact movingFrequencyCore_values_modEq value w F E T R hf hcomp hR hv
    XL XR XL XR (Int.ModEq.refl _) (Int.ModEq.refl _)

end Ostmann

end OAI
