import OAI.MeasureTheory.Falconer.Fourier.LaplacianFourier
import OAI.MeasureTheory.Falconer.Fourier.OscillatoryTaylor

namespace OAI

/-! Taylor expansion in the squared Euclidean radius. -/

namespace Falconer
open MeasureTheory
open PlanarFalconer (imaginaryExponential imaginaryTaylor)
open scoped FourierTransform SchwartzMap

theorem schwartz_radius_power_integrable {n : ℕ} (φ : 𝓢(Space n, ℂ)) (j : ℕ) :
    Integrable (fun x : Space n => ((‖x‖^2 : ℝ) : ℂ)^j * φ x) := by
  apply (φ.integrable_pow_mul volume (2*j)).mono' (by fun_prop)
  filter_upwards with x
  simp [norm_pow, Complex.norm_real, pow_mul]

theorem imaginaryTaylor_radius_integrable {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ) (β : ℝ) :
    Integrable (fun x : Space n => imaginaryTaylor K (β*‖x‖^2) * φ x) := by
  have he : (fun x : Space n => imaginaryTaylor K (β*‖x‖^2)*φ x) =
      fun x => ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          (((‖x‖^2 : ℝ) : ℂ)^j * φ x) := by
    funext x
    unfold imaginaryTaylor
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, mul_pow]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j _ => (schwartz_radius_power_integrable φ j).const_mul _)

theorem imaginaryExponential_radius_integrable {n : ℕ} (φ : 𝓢(Space n, ℂ)) (β : ℝ) :
    Integrable (fun x : Space n => imaginaryExponential (β*‖x‖^2) * φ x) := by
  apply φ.integrable.norm.mono' (by unfold imaginaryExponential; fun_prop)
  filter_upwards with x
  have h := PlanarFalconer.imaginaryExponential_derivative_norm 0 (β*‖x‖^2)
  simp only [iteratedDeriv_zero] at h
  rw [norm_mul, h, one_mul]

theorem radial_taylor_integral_bound {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) :
    ‖(∫ x : Space n, imaginaryExponential (β*‖x‖^2)*φ x) -
      (∫ x : Space n, imaginaryTaylor K (β*‖x‖^2)*φ x)‖ ≤
      (β^(K+1)/(K.factorial : ℝ)) *
        ∫ x : Space n, ‖x‖^(2*(K+1))*‖φ x‖ := by
  rw [← integral_sub (imaginaryExponential_radius_integrable φ β)
    (imaginaryTaylor_radius_integrable φ K β), ← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((φ.integrable_pow_mul volume (2*(K+1))).const_mul _) _
  filter_upwards with x
  rw [← sub_mul, norm_mul]
  calc
    _ ≤ ((β*‖x‖^2)^(K+1)/(K.factorial : ℝ))*‖φ x‖ :=
      mul_le_mul_of_nonneg_right (PlanarFalconer.imaginaryExponential_taylor_bound K
        (mul_nonneg hβ (sq_nonneg _))) (norm_nonneg _)
    _ = _ := by rw [mul_pow, pow_mul]; ring

theorem radial_taylor_integral {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ) (β : ℝ) :
    (∫ x : Space n, imaginaryTaylor K (β*‖x‖^2)*φ x) =
      ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          ∫ x : Space n, ((‖x‖^2 : ℝ) : ℂ)^j * φ x := by
  have he : (fun x : Space n => imaginaryTaylor K (β*‖x‖^2)*φ x) =
      fun x => ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          (((‖x‖^2 : ℝ) : ℂ)^j * φ x) := by
    funext x
    unfold imaginaryTaylor
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, mul_pow]
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact integral_const_mul _ _
  · intro j _
    exact (schwartz_radius_power_integrable φ j).const_mul _

theorem radial_taylor_inverse_integral {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ) (β : ℝ) :
    (∫ x : Space n, imaginaryTaylor K (β*‖x‖^2)*𝓕⁻ φ x) =
      ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          (((-(2 * (Real.pi : ℂ))^2)^j)⁻¹ *
            ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
              (φ : Space n → ℂ)) 0) := by
  rw [radial_taylor_integral]
  simp only [inverse_fourier_radial_moment]

end Falconer

end OAI
