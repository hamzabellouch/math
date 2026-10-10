import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2Multiplier

namespace OAI

/-! Small uniform changes of the mass weight give small changes of its L² multiplier. -/

open MeasureTheory
namespace DefocusingNLS

theorem spectralL2Weight_difference_norm (μ : Measure ℝ) (q p : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (hp : AEStronglyMeasurable p μ)
    (M N : ℝ) (hbq : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (hbp : ∀ᵐ r ∂μ, ‖p r‖ ≤ N)
    (δ : ℝ) (hδ : ∀ᵐ r ∂μ, ‖q r-p r‖ ≤ δ) (u : Lp ℂ 2 μ) :
    ‖spectralL2Multiplier μ q hq M hbq u-spectralL2Multiplier μ p hp N hbp u‖ ≤ δ*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (spectralL2Multiplier μ q hq M hbq u)
      (spectralL2Multiplier μ p hp N hbp u),spectralL2Weight_ae μ q hq M hbq u,
      spectralL2Weight_ae μ p hp N hbp u,hδ] with r hsub hqv hpv hdiff
  change spectralL2Multiplier μ q hq M hbq u r=q r • u r at hqv
  change spectralL2Multiplier μ p hp N hbp u r=p r • u r at hpv
  rw [hsub,Pi.sub_apply,hqv,hpv,← sub_smul,norm_smul]
  exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)

theorem spectralL2Weight_inner_difference (μ : Measure ℝ) (q p : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (hp : AEStronglyMeasurable p μ)
    (M N : ℝ) (hbq : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (hbp : ∀ᵐ r ∂μ, ‖p r‖ ≤ N)
    (δ : ℝ) (hδ : ∀ᵐ r ∂μ, ‖q r-p r‖ ≤ δ) (u v : Lp ℂ 2 μ) :
    ‖inner ℝ (spectralL2Multiplier μ q hq M hbq u) v-
        inner ℝ (spectralL2Multiplier μ p hp N hbp u) v‖ ≤ δ*‖u‖*‖v‖ := by
  rw [← inner_sub_left]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul_of_nonneg_right (spectralL2Weight_difference_norm μ q p hq hp M N hbq hbp δ hδ u)
      (norm_nonneg _))

end DefocusingNLS

end OAI
