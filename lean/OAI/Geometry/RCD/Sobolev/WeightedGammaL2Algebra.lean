import OAI.Geometry.RCD.Sobolev.GammaL2Bound
import OAI.Geometry.RCD.Sobolev.WeightedGammaGradientBound

namespace OAI

/-! # Bilinearity of mixed Bochner terms with L² Laplacians -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weightedGamma_lp_add_weight (d e : Lp ℝ 2 μ) (f w : SobolevSpace μ hQ)
    (L : ℝ≥0) (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x≤L) :
    weightedGamma μ hQ (d+e : Lp ℝ 2 μ) f w = weightedGamma μ hQ d f w+weightedGamma μ hQ e f w := by
  have hi (q : Lp ℝ 2 μ) : Integrable (fun x => q x*localGamma μ hQ f w x) μ :=
    (Lp.memLp q).integrable_mul (localGamma_memLp_of_bounded_gradient μ hQ f w L hf)
  unfold weightedGamma
  rw [← integral_add (hi d) (hi e)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add d e] with x hx
  rw [hx]
  simp only [Pi.add_apply]
  ring

omit [ProperSpace X] in
theorem weightedGamma_lp_smul_weight (d : Lp ℝ 2 μ) (c : ℝ) (f w : SobolevSpace μ hQ) :
    weightedGamma μ hQ (c • d : Lp ℝ 2 μ) f w = c*weightedGamma μ hQ d f w := by
  unfold weightedGamma
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c d] with x hx
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

theorem weightedGamma_lp_add_left (d : Lp ℝ 2 μ) (f g w : SobolevSpace μ hQ)
    (L M : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x≤L)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ g x≤M) :
    weightedGamma μ hQ d (f+g) w = weightedGamma μ hQ d f w+weightedGamma μ hQ d g w := by
  have hi : Integrable (fun x => d x*localGamma μ hQ f w x) μ := (Lp.memLp d).integrable_mul (localGamma_memLp_of_bounded_gradient μ hQ f w L hf)
  have hj : Integrable (fun x => d x*localGamma μ hQ g w x) μ := (Lp.memLp d).integrable_mul (localGamma_memLp_of_bounded_gradient μ hQ g w M hg)
  unfold weightedGamma
  rw [← integral_add hi hj]
  apply integral_congr_ae
  filter_upwards [localGamma_add_left μ hQ f g w] with x hx
  rw [hx,mul_add]

/-- The full mixed source of two regular directions is symmetric after
polarization; this expansion retains L² Laplacians without requiring
bounded Laplacians. -/
theorem weightedGamma_lp_diagonal_add (d e : Lp ℝ 2 μ) (f g w : SobolevSpace μ hQ)
    (L M : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x≤L)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ g x≤M) :
    weightedGamma μ hQ (d+e : Lp ℝ 2 μ) (f+g) w =
      weightedGamma μ hQ d f w+weightedGamma μ hQ d g w+
      weightedGamma μ hQ e f w+weightedGamma μ hQ e g w := by
  rw [weightedGamma_lp_add_left μ hQ (d+e) f g w L M hf hg,
    weightedGamma_lp_add_weight μ hQ d e f w L hf,
    weightedGamma_lp_add_weight μ hQ d e g w M hg]
  ring

end RegularPointCoordinates

end

end OAI
