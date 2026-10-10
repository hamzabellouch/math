import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierSeries

namespace OAI

/-! # Convolution of a periodic Fourier series by a Schwartz function -/

open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem spatialFourierCharacter_sub_scale (L : ℝ) (n : frequencyLattice) (y z : E) :
    spatialFourierCharacter n (L⁻¹ • (y - z)) =
      spatialFourierCharacter n (L⁻¹ • y) *
        Complex.exp ((-⟪z, L⁻¹ • (n : E)⟫ : ℝ) * Complex.I) := by
  unfold spatialFourierCharacter
  rw [← Complex.exp_add, smul_sub, inner_sub_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left]
  congr 1
  push_cast
  ring

theorem hasSum_schwartzFourierConvolution (L : ℝ) (K : 𝓢(E, ℂ))
    (v : frequencyLattice → ℂ) (hv : Summable (fun n => ‖v n‖)) (y : E) :
    HasSum (fun n : frequencyLattice => (radianFourierKernel K (L⁻¹ • (n : E)) * v n) *
      spatialFourierCharacter n (L⁻¹ • y))
      (∫ z : E, K z * spatialFourierSeries v (L⁻¹ • (y - z))) := by
  let G : frequencyLattice → E → ℂ := fun n z =>
    K z * (v n * spatialFourierCharacter n (L⁻¹ • (y - z)))
  have hnorm (n : frequencyLattice) (z : E) : ‖G n z‖ = ‖K z‖ * ‖v n‖ := by
    simp only [G, norm_mul, spatialFourierCharacter_norm, mul_one]
  have hG (n : frequencyLattice) : Integrable (G n) := by
    apply (K.integrable.norm.mul_const ‖v n‖).mono'
    · exact (K.continuous.mul (continuous_const.mul
        ((continuous_spatialFourierCharacter n).comp
          ((continuous_const.sub continuous_id).const_smul L⁻¹)))).aestronglyMeasurable
    · exact ae_of_all _ (fun z => (hnorm n z).le)
  have hGI : Summable (fun n => ∫ z : E, ‖G n z‖) := by
    have he (n : frequencyLattice) : (∫ z : E, ‖G n z‖) =
        (∫ z : E, ‖K z‖) * ‖v n‖ := by
      simp_rw [hnorm]
      exact integral_mul_const _ _
    simpa only [he] using hv.mul_left (∫ z : E, ‖K z‖)
  have hs := hasSum_integral_of_summable_integral_norm hG hGI
  have hp (z : E) : (∑' n, G n z) =
      K z * spatialFourierSeries v (L⁻¹ • (y - z)) := by
    simp only [G, spatialFourierSeries, tsum_mul_left]
  have ht (n : frequencyLattice) : (∫ z : E, G n z) =
      (radianFourierKernel K (L⁻¹ • (n : E)) * v n) *
        spatialFourierCharacter n (L⁻¹ • y) := by
    have he (z : E) : G n z = (v n * spatialFourierCharacter n (L⁻¹ • y)) *
        (Complex.exp ((-⟪z, L⁻¹ • (n : E)⟫ : ℝ) * Complex.I) * K z) := by
      dsimp only [G]
      rw [spatialFourierCharacter_sub_scale]
      ring
    simp_rw [he]
    rw [integral_const_mul, ← radianFourierIntegral, ← radianFourierKernel_apply]
    ring
  simpa only [ht, hp] using hs

theorem schwartzFourierConvolution_eq (L : ℝ) (K : 𝓢(E, ℂ))
    (v : frequencyLattice → ℂ) (hv : Summable (fun n => ‖v n‖)) (y : E) :
    spatialFourierSeries (fun n => radianFourierKernel K (L⁻¹ • (n : E)) * v n)
      (L⁻¹ • y) = ∫ z : E, K z * spatialFourierSeries v (L⁻¹ • (y - z)) :=
  (hasSum_schwartzFourierConvolution L K v hv y).tsum_eq

theorem radianFourierKernel_norm_le_integral (K : 𝓢(E, ℂ)) (ξ : E) :
    ‖radianFourierKernel K ξ‖ ≤ ∫ z : E, ‖K z‖ := by
  rw [radianFourierKernel_apply, radianFourierIntegral]
  calc
    _ ≤ ∫ z : E, ‖Complex.exp ((-⟪z, ξ⟫ : ℝ) * Complex.I) * K z‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

end DefocusingNLS

end OAI
