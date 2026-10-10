import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # A mixed Gamma bound with only an L² weight -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weightedGamma_le_of_bounded_gradient (d : Lp ℝ 2 μ)
    (f w : SobolevSpace μ hQ) (L : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L) :
    |weightedGamma μ hQ d f w| ≤
      (L : ℝ) * ‖d‖ * ‖SobolevSpace.minimalSlope μ hQ w‖ := by
  let G := SobolevSpace.minimalSlope μ hQ w
  have hG0 : ∀ᵐ x ∂μ, 0 ≤ G x :=
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ w)
  have hre : (fun x => lpAbs μ d x * G x) =ᵐ[μ] fun x => |d x| * G x := by
    filter_upwards [lpAbs_coe μ d] with x hx
    rw [hx]
  have hi : Integrable (fun x => |d x| * G x) μ :=
    ((Lp.memLp (lpAbs μ d)).integrable_mul (Lp.memLp G)).congr hre
  have hnorm : |weightedGamma μ hQ d f w| ≤ ∫ x, (L : ℝ) * (|d x| * G x) ∂μ := by
    rw [← Real.norm_eq_abs]
    unfold weightedGamma
    apply norm_integral_le_of_norm_le (hi.const_mul (L : ℝ))
    filter_upwards [localGamma_abs_le μ hQ f w, hf, hG0] with x hΓ hf' hG'
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |d x| * |localGamma μ hQ f w x| ≤
          |d x| * (SobolevSpace.minimalSlope μ hQ f x * G x) :=
        mul_le_mul_of_nonneg_left hΓ (abs_nonneg _)
      _ ≤ |d x| * ((L : ℝ) * G x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf' hG') (abs_nonneg _)
      _ = (L : ℝ) * (|d x| * G x) := by ring
  have he : (∫ x, |d x| * G x ∂μ) = inner ℝ (lpAbs μ d) G := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpAbs_coe μ d] with x hx
    simp only [Real.inner_apply, hx]
  rw [integral_const_mul, he] at hnorm
  have hinner : inner ℝ (lpAbs μ d) G ≤ ‖d‖ * ‖G‖ := by
    calc
      _ ≤ |inner ℝ (lpAbs μ d) G| := le_abs_self _
      _ ≤ ‖lpAbs μ d‖ * ‖G‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (lpAbs μ d) G
      _ = _ := by rw [lpAbs_norm]
  exact hnorm.trans (by nlinarith [mul_le_mul_of_nonneg_left hinner L.coe_nonneg])

end RegularPointCoordinates

end

end OAI
