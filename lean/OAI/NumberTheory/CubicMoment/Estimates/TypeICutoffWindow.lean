import OAI.NumberTheory.CubicMoment.Estimates.TypeIHeightIntegral

namespace OAI

/-! The actual cutoff window of the Type-I polynomial is the difference
of its two normalized endpoint integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def typeIHeightPolynomial {γ : Type*} (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ) (ℓ : ℤ) (U t : ℝ) : ℂ :=
  ∑ r ∈ S, (α r*normTwist t r)*metaplecticAngularSmoothSum r ℓ (W (w r)) U t

lemma continuous_typeIHeightPolynomial {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {U : ℝ} (hU : 0 < U) :
    Continuous (typeIHeightPolynomial w S α W ℓ U) := by
  apply continuous_finsetSum
  intro r _
  exact (continuous_const.mul (continuous_normTwist r)).mul
    (continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ (W (w r)) hU
      (le_refl (Real.exp hW.radius*U)) (hW.upper_support (w r)))

def typeICutoffWindow {γ : Type*} (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ) (ℓ : ℤ) (U H T X₀ : ℝ) : ℂ :=
  ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
      Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*typeIHeightPolynomial w S α W ℓ U t

theorem typeICutoffWindow_endpoints {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {U T X₀ : ℝ} (hU : 0 < U) (hT : 0 < T)
    (hX₀ : 0 < X₀) (H : ℝ) :
    typeICutoffWindow w S α W ℓ U H T X₀ =
      typeIHeightIntegral w S α W ℓ U H T X₀-
        typeIHeightIntegral w S α W ℓ U H T (2*X₀) := by
  let f := typeIHeightPolynomial w S α W ℓ U
  have hf : Continuous f := continuous_typeIHeightPolynomial hW w S α ℓ hU
  have hi (Y : ℝ) : Integrable (fun t : ℝ =>
      (localizedEndpointWeight H T t*Complex.exp ((-Real.log Y*t:ℝ)*Complex.I))*f t) := by
    have he : Continuous (fun t : ℝ => Complex.exp ((-Real.log Y*t:ℝ)*Complex.I)) := by
      fun_prop
    exact (((localizedEndpointWeight_smooth H hT).continuous.mul he).mul hf).integrable_of_hasCompactSupport
      ((localizedEndpointWeight_compact H hT).mul_right.mul_right)
  change (∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
    Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*f t) =
      (T:ℂ)⁻¹*(∫ t : ℝ, (localizedEndpointWeight H T t*
        Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*f t)-
      (T:ℂ)⁻¹*(∫ t : ℝ, (localizedEndpointWeight H T t*
        Complex.exp ((-Real.log (2*X₀)*t:ℝ)*Complex.I))*f t)
  rw [←mul_sub,←integral_sub (hi X₀) (hi (2*X₀)),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [cutoffHeightMultiplier_window_endpoints H hT t]
  have he : Complex.exp ((-Real.log (2*X₀)*t:ℝ)*Complex.I) =
      Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        Complex.exp ((-Real.log 2*t:ℝ)*Complex.I) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX₀.ne',←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem typeICutoffWindow_le_mean {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {U T X₀ : ℝ} (hU : 0 < U) (hT : 0 < T)
    (hX₀ : 0 < X₀) (H : ℝ) :
    ‖typeICutoffWindow w S α W ℓ U H T X₀‖ ≤
      2*dyadicHeightMean (fun t => ∑ r ∈ S,
        ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖) T := by
  rw [typeICutoffWindow_endpoints hW w S α ℓ hU hT hX₀ H]
  apply (norm_sub_le _ _).trans
  have h₁ := typeIHeightIntegral_le_mean hW w S α ℓ hU hT H X₀
  have h₂ := typeIHeightIntegral_le_mean hW w S α ℓ hU hT H (2*X₀)
  linarith

end CubicFirstMoment

end

end OAI
