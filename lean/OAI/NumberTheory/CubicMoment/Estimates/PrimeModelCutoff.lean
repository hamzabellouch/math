import OAI.NumberTheory.CubicMoment.Estimates.HeightEndpointRegularity
import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelHeight

namespace OAI

/-! The undecomposed prime model in the actual cutoff windows. The
power saving comes from ordinary mean value, with the endpoint phases
and the angular character retained exactly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_cutoff_window_endpoints (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (H : ℝ) {T X₀ : ℝ} (hT : 0 < T) (hX₀ : 0 < X₀) :
    (∑ p ∈ P, c p*heightFourierIntegral
      (fun t => cutoffHeightMultiplier H t*heightWindow T t)
        (Real.log (norm p)-Real.log X₀)) =
      (T:ℂ)⁻¹*((∫ t : ℝ,
        (localizedEndpointWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
          ∑ p ∈ P, c p*normTwist t p) -
        (∫ t : ℝ,
        (localizedEndpointWeight H T t*Complex.exp ((-Real.log (2*X₀)*t:ℝ)*Complex.I))*
          ∑ p ∈ P, c p*normTwist t p)) := by
  have he (p : Eisenstein) : Real.log (norm p)-Real.log X₀-Real.log 2 =
      Real.log (norm p)-Real.log (2*X₀) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX₀.ne']
    ring
  calc
    _ = (T:ℂ)⁻¹*((∑ p ∈ P, c p*heightFourierIntegral (localizedEndpointWeight H T)
          (Real.log (norm p)-Real.log X₀)) -
        ∑ p ∈ P, c p*heightFourierIntegral (localizedEndpointWeight H T)
          (Real.log (norm p)-Real.log (2*X₀))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [cutoff_window_fourier_endpoints H hT, he]
      ring
    _ = _ := by
      have h₁ := height_norm_polynomial_integral P c id _
        (localizedEndpointWeight_integrable H hT) (Real.log X₀)
      have h₂ := height_norm_polynomial_integral P c id _
        (localizedEndpointWeight_integrable H hT) (Real.log (2*X₀))
      simp only [id_eq] at h₁ h₂
      rw [h₁,h₂]

theorem prime_model_cutoff_power_saving {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T M δ X₀ : ℝ} (H : ℝ) (hX : 1 ≤ X) (hX₀ : 0 < X₀)
    (hTX : T ≤ X) (hTδ : X^δ ≤ T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) :
    ‖∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
      heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
        (Real.log (norm p)-Real.log X₀)‖ ≤
      4*Real.sqrt (720*C)*M*X^(5/6-δ/2) := by
  have hT : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) δ).trans_le hTδ
  let f := fun t => dispersionModel P (fun p => c p*theta ℓ p) t
  have hf : Continuous f := by
    simpa only [add_zero] using continuous_prime_model_height P c ℓ 0
  have hmean : dyadicHeightMean (fun t => ‖f t‖) T ≤
      2*Real.sqrt (720*C)*M*X^(5/6-δ/2) := by
    simpa only [add_zero] using prime_model_height_power_saving hMV hC P c
      hX hTX hTδ hM hP hc ℓ 0
  have hpiece (Y : ℝ) :
      ‖(T:ℂ)⁻¹*(∫ t : ℝ,
        (localizedEndpointWeight H T t*Complex.exp ((-Real.log Y*t:ℝ)*Complex.I))*f t)‖ ≤
      2*Real.sqrt (720*C)*M*X^(5/6-δ/2) := by
    apply (normalized_dyadicWeightIntegral_bound f _ hf hT (by norm_num : (0:ℝ) ≤ 1) ?_ ?_).trans
      (by simpa only [one_mul] using hmean)
    · intro t
      have he : ‖Complex.exp ((-Real.log Y*t:ℝ)*Complex.I)‖ = 1 := by
        simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_self, Real.exp_zero]
      rw [norm_mul, he, mul_one]
      exact localizedEndpointWeight_norm_le H hT t
    · intro t ht
      rw [localizedEndpointWeight_zero H hT t ht, zero_mul]
  rw [finite_cutoff_window_endpoints P _ H hT hX₀]
  have he (t : ℝ) :
      (∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*normTwist t p) = f t := by
    unfold f dispersionModel
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp_rw [he]
  rw [mul_sub]
  exact (norm_sub_le _ _).trans ((add_le_add (hpiece X₀) (hpiece (2*X₀))).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
