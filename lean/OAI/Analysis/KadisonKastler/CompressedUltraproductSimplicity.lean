import OAI.Analysis.KadisonKastler.NormUltraproductSimplicity
import OAI.Analysis.KadisonKastler.PositiveCompressionFullness

namespace OAI

/-! # Positive compressions imply simplicity of the norm ultraproduct -/

namespace KadisonKastler

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, PartialOrder (B j)] [∀ j, StarOrderedRing (B j)]

theorem normUltraproduct_simple_of_positive_compressions
    (hcompress : ∀ j (x : B j) (ε : ℝ), 0 < ε → ε ≤ ‖x‖ →
      ∃ v : B j, star v * v = 1 ∧
        algebraMap ℝ (B j) (ε ^ 2 / 2) ≤ star v * (star x * x) * v)
    (ω : Ultrafilter ℕ) : CStarSimple (NormUltraproduct B ω) := by
  apply normUltraproduct_simple_of_uniform_fullness
  intro ε R hε hR
  let t := ε ^ 2 / 2
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨t⁻¹ * R + 1, by positivity, ?_⟩
  intro j x hx hRx
  obtain ⟨v, hv, hq⟩ := hcompress j x ε hε hx
  obtain ⟨b, c, hb, hc, hbc⟩ :=
    exists_fullness_factors_of_positive_compression x v hv ht hq
  refine ⟨b, c, ?_, ?_, hbc⟩
  · exact hb.trans ((mul_le_mul_of_nonneg_left hRx (inv_nonneg.mpr ht.le)).trans
      (le_add_of_nonneg_right zero_le_one))
  · exact hc.trans (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr ht.le) hR))

end

end KadisonKastler

end OAI
