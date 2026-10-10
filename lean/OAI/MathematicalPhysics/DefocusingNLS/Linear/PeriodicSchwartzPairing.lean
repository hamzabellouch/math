import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzFourierConvolution

namespace OAI

/-! # Schwartz testing of absolutely convergent periodic Fourier series -/

open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasSum_periodicSchwartzPairing (L : ℝ) (ψ : 𝓢(E, ℂ))
    (c : frequencyLattice → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    HasSum (fun n => c n * radianFourierKernel ψ (-(L⁻¹ • (n : E))))
      (∫ y : E, ψ y * spatialFourierSeries c (L⁻¹ • y)) := by
  let G := fun (n : frequencyLattice) (y : E) =>
    ψ y * (c n * spatialFourierCharacter n (L⁻¹ • y))
  have hn (n : frequencyLattice) (y : E) : ‖G n y‖ = ‖ψ y‖ * ‖c n‖ := by
    simp only [G, norm_mul, spatialFourierCharacter_norm, mul_one]
  have hi (n : frequencyLattice) : Integrable (G n) := by
    apply (ψ.integrable.norm.mul_const ‖c n‖).mono'
    · exact (ψ.continuous.mul (continuous_const.mul
        ((continuous_spatialFourierCharacter n).comp (continuous_const_smul L⁻¹)))).aestronglyMeasurable
    · exact ae_of_all _ (fun y => (hn n y).le)
  have hs : Summable (fun n => ∫ y : E, ‖G n y‖) := by
    simp_rw [hn, integral_mul_const]
    exact hc.mul_left _
  have h := hasSum_integral_of_summable_integral_norm hi hs
  have he (n : frequencyLattice) : (∫ y : E, G n y) =
      c n * radianFourierKernel ψ (-(L⁻¹ • (n : E))) := by
    rw [radianFourierKernel_apply, radianFourierIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [G, spatialFourierCharacter]
    rw [inner_neg_right, neg_neg, real_inner_smul_left, real_inner_smul_right]
    ring
  simpa only [he, G, spatialFourierSeries, tsum_mul_left] using h

theorem integrable_periodicSchwartzPairing (L : ℝ) (ψ : 𝓢(E, ℂ))
    (c : frequencyLattice → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    Integrable (fun y : E => ψ y * spatialFourierSeries c (L⁻¹ • y)) := by
  apply ψ.integrable.mul_bdd
    (((continuous_spatialFourierSeries c hc).comp (continuous_const_smul L⁻¹)).aestronglyMeasurable)
  exact ae_of_all _ (fun y => spatialFourierSeries_norm_le c hc (L⁻¹ • y))

end DefocusingNLS

end OAI
