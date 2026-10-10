import OAI.Analysis.KadisonKastler.FrequencySupport
import OAI.Analysis.KadisonKastler.RealNestMultiplier

namespace OAI

/-! # The concrete algebra of positive-frequency multipliers -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Decomposable operators preserving the actual positive-frequency cut.
Commutation with characters is included so the published causal multiplier
theorem applies after Fourier conjugation. -/
def positiveFrequencyAlgebra : Subalgebra ℂ
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  carrier := {T | (∀ s : ℝ, Commute T (regularCharacterUnitary (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) ∧
    regularFrequencyProjection 0 * T * regularFrequencyProjection 0 =
      T * regularFrequencyProjection 0}
  zero_mem' := by simp [Commute, SemiconjBy]
  one_mem' := by
    refine ⟨fun _ => Commute.one_left _, ?_⟩
    simpa only [mul_one, one_mul] using
      (regularFrequencyProjection_isStarProjection (H := H) 0).isIdempotentElem.eq
  add_mem' := by
    rintro A B ⟨hA, hAP⟩ ⟨hB, hBP⟩
    exact ⟨fun s => (hA s).add_left (hB s), by
      simp only [mul_add, add_mul, hAP, hBP]⟩
  mul_mem' := by
    rintro A B ⟨hA, hAP⟩ ⟨hB, hBP⟩
    refine ⟨fun s => (hA s).mul_left (hB s), ?_⟩
    let P : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := regularFrequencyProjection 0
    change P * (A * B) * P = (A * B) * P
    change P * A * P = A * P at hAP
    change P * B * P = B * P at hBP
    calc
      _ = P * A * (B * P) := by simp only [mul_assoc]
      _ = P * A * (P * B * P) := congrArg (fun Z => P * A * Z) hBP.symm
      _ = (P * A * P) * B * P := by simp only [mul_assoc]
      _ = (A * P) * B * P := by rw [hAP]
      _ = A * (P * B * P) := by simp only [mul_assoc]
      _ = A * (B * P) := congrArg (fun Z => A * Z) hBP
      _ = _ := by simp only [mul_assoc]
  algebraMap_mem' z := by
    refine ⟨fun s => ?_, ?_⟩
    · change algebraMap ℂ _ z * _ = _ * algebraMap ℂ _ z
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
    · simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm,
        smul_mul_assoc, mul_one, one_mul,
        (regularFrequencyProjection_isStarProjection (H := H) 0).isIdempotentElem.eq]

/-- A nest-preserving represented field is an element of the concrete
positive-frequency multiplier algebra. -/
theorem regularFieldOperator_mem_positiveFrequencyAlgebra
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, MeasureTheory.AEStronglyMeasurable (fun t => F t x) MeasureTheory.volume)
    (C : ℝ) (hC : ∀ᵐ t ∂MeasureTheory.volume, ‖F t‖ ≤ C)
    (hpres : PreservesProjectionNest regularFrequencyNest
      (regularFieldOperator MeasureTheory.volume F hF C hC)) :
    regularFieldOperator MeasureTheory.volume F hF C hC ∈
      positiveFrequencyAlgebra (H := H) := by
  refine ⟨regularFieldOperator_commutes_character F hF C hC, ?_⟩
  have hp := hpres 0
  simp only [regularFrequencyNest, neg_zero] at hp
  rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at hp
  exact hp.symm

end

end KadisonKastler

end OAI
