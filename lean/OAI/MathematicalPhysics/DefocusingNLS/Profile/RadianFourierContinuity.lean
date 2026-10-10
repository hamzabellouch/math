import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierLocalization

namespace OAI

/-! # Continuity and linearity of the radian Fourier integral

These statements apply directly to integrable physical functions, including
localized expanding-torus data.
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radianFourierIntegral_eq_fourier (f : E → ℂ) (ξ : E) :
    radianFourierIntegral f ξ = 𝓕 f ((2 * Real.pi)⁻¹ • ξ) := by
  rw [Real.fourier_eq']
  unfold radianFourierIntegral
  apply integral_congr_ae
  filter_upwards [] with y
  rw [real_inner_smul_right]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  field_simp

theorem continuous_radianFourierIntegral {f : E → ℂ} (hf : Integrable f) :
    Continuous (radianFourierIntegral f) := by
  have hF : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have he : radianFourierIntegral f = (fun ξ => 𝓕 f ((2 * Real.pi)⁻¹ • ξ)) :=
    funext (radianFourierIntegral_eq_fourier f)
  rw [he]
  exact hF.comp (continuous_const_smul ((2 * Real.pi)⁻¹))

private theorem integrable_radianFourierIntegrand {f : E → ℂ}
    (hf : Integrable f) (ξ : E) :
    Integrable (fun y => Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) * f y) := by
  apply hf.bdd_mul (c := 1) (by fun_prop)
  exact Filter.Eventually.of_forall (fun y => (Complex.norm_exp_ofReal_mul_I _).le)

theorem radianFourierIntegral_add {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) :
    radianFourierIntegral (f + g) = radianFourierIntegral f + radianFourierIntegral g := by
  funext ξ
  simp only [radianFourierIntegral, Pi.add_apply, mul_add]
  exact integral_add (integrable_radianFourierIntegrand hf ξ)
    (integrable_radianFourierIntegrand hg ξ)

theorem radianFourierIntegral_smul (c : ℂ) (f : E → ℂ) :
    radianFourierIntegral (c • f) = c • radianFourierIntegral f := by
  funext ξ
  simp only [radianFourierIntegral, Pi.smul_apply, smul_eq_mul]
  have heq (y : E) :
      Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) * (c * f y) =
        c * (Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) * f y) := by ring
  simp_rw [heq]
  exact integral_const_mul _ _

end DefocusingNLS

end OAI
