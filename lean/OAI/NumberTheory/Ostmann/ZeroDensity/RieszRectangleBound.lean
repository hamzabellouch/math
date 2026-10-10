import OAI.NumberTheory.Ostmann.ZeroDensity.RieszTruncation
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszLeftEstimate

namespace OAI

/-! # A quantitative Riesz estimate from a zero-free rectangle -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem characterRieszMean_rectangle_bound : ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (X a b T M : ℝ),
      1 ≤ X → 1 / 2 ≤ a → a ≤ b → 1 < b → b ≤ 2 → 0 < T → 0 ≤ M →
      (∀ z ∈ uIcc a b ×ℂ uIcc (-T) T, χ.L z ≠ 0) →
      (∀ z ∈ uIcc a b ×ℂ uIcc (-T) T, ‖logDeriv χ.L z‖ ≤ M) →
      ‖characterRieszMean χ X‖ ≤ K * M * X ^ a +
        2 * (M * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + C) * X ^ b / T := by
  obtain ⟨K, hK, hleft⟩ := leftRieszIntegrand_segment_bound
  obtain ⟨C, hC, htrunc⟩ := characterRieszMean_truncation
  refine ⟨K, C, hK, hC, ?_⟩
  intro χ X a b T M hX ha hab hb hb2 hT hM hne hbound
  have hXp : 0 < X := by linarith
  have hpt (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : t ∈ Icc (-T) T) :
      ‖logDeriv χ.L ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M := by
    apply hbound _ ⟨?_, ?_⟩
    · simpa [uIcc_of_le hab] using hσ
    · simpa [uIcc_of_le (show -T ≤ T by linarith)] using ht
  have hl := hleft χ X a T M hXp ha hM (fun t ht => hpt a t ⟨le_rfl, hab⟩ ht)
  have hl' : ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ ≤ K * M * X ^ a := by
    simpa only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
      integral_Icc_eq_integral_Ioc] using hl
  have hu := riesz_horizontal_segment_bound χ X a b T M hX hab
    (by rwa [abs_of_pos hT]) hM (fun σ hσ => hpt σ T hσ ⟨by linarith, le_rfl⟩)
  have hd := riesz_horizontal_segment_bound χ X a b (-T) M hX hab
    (by rwa [abs_neg, abs_of_pos hT]) hM (fun σ hσ => hpt σ (-T) hσ ⟨le_rfl, by linarith⟩)
  rw [neg_sq] at hd
  have hz := rieszContour_rectangle_zero χ X hXp a b (-T) T (by linarith) hab hne
  have hv := rectangle_vertical_shift_norm_bound _ a b (-T) T hz
  change ‖∫ t in -T..T, rightRieszIntegrand χ X b t‖ ≤
    ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ + _ + _ at hv
  have hm := htrunc χ X b T hXp hb hb2 hT
  linarith

end Ostmann

end OAI
