import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorFourier

namespace OAI

/-! # The high-frequency gain for the physical derivative commutator

For a Schwartz input with frequencies above R, the actual commutator costs
only R⁻¹ times its top homogeneous energy. The coefficient is an explicit
integrable Fourier moment of the fixed Schwartz potential.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem two_add_pow_le (N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (2 + r) ^ N ≤ 3 ^ N * (1 + r ^ N) := by
  by_cases h : r ≤ 1
  · calc
      _ ≤ (3 : ℝ) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ _ := by nlinarith [pow_nonneg hr N, pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) N]
  · have h1 : 1 ≤ r := le_of_lt (lt_of_not_ge h)
    calc
      _ ≤ (3 * r) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 3 ^ N * r ^ N := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) N]

noncomputable def homogeneousCommutatorMoment (N : ℕ) (V : 𝓢(E, ℂ)) (ξ : E) : ℝ :=
  (N + 1 : ℕ) * (3 : ℝ) ^ N * (‖ξ‖ + ‖ξ‖ ^ (N + 1)) * ‖radianFourierKernel V ξ‖

theorem homogeneousCommutatorMoment_nonneg (N : ℕ) (V : 𝓢(E, ℂ)) (ξ : E) :
    0 ≤ homogeneousCommutatorMoment N V ξ := by
  unfold homogeneousCommutatorMoment
  positivity

theorem homogeneousCommutatorMoment_integrable (N : ℕ) (V : 𝓢(E, ℂ)) :
    Integrable (homogeneousCommutatorMoment N V) := by
  have h := (((radianFourierKernel V).integrable_pow_mul volume 1).add
    ((radianFourierKernel V).integrable_pow_mul volume (N + 1))).const_mul
      ((N + 1 : ℕ) * (3 : ℝ) ^ N)
  convert h using 1
  funext ξ
  simp only [homogeneousCommutatorMoment, pow_one, Pi.add_apply]
  ring

private theorem commutator_integrand_high (N : ℕ) (j : Fin (N + 1) → Fin 12)
    (V f : 𝓢(E, ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hf : ∀ η : E, ‖η‖ < R → radianFourierKernel f η = 0) (ξ η : E) :
    ‖(homogeneousOrderedSymbol (N + 1) j ξ -
        homogeneousOrderedSymbol (N + 1) j (ξ - η)) *
      radianFourierKernel V η * radianFourierKernel f (ξ - η)‖ ≤
      R⁻¹ * (homogeneousCommutatorMoment N V η *
        homogeneousFourierMagnitude (N + 1) (radianFourierKernel f) (ξ - η)) := by
  by_cases h : ‖ξ - η‖ < R
  · rw [hf _ h, mul_zero, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ R))
      (mul_nonneg (homogeneousCommutatorMoment_nonneg _ _ _)
        (homogeneousFourierMagnitude_nonneg _ _ _))
  · have hs := homogeneousOrderedSymbol_highFrequency N j ξ (ξ - η) R hR (le_of_not_gt h)
    rw [sub_sub_cancel] at hs
    have ht := two_add_pow_le N ‖η‖ (norm_nonneg _)
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (N + 1 : ℕ) / R * ‖η‖))
        (pow_nonneg (norm_nonneg (ξ - η)) (N + 1)))
      (mul_nonneg (norm_nonneg (radianFourierKernel V η))
        (norm_nonneg (radianFourierKernel f (ξ - η))))
    have hh := mul_le_mul_of_nonneg_right hs
      (mul_nonneg (norm_nonneg (radianFourierKernel V η))
        (norm_nonneg (radianFourierKernel f (ξ - η))))
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (((N + 1 : ℕ) / R) * ‖η‖ * (2 + ‖η‖) ^ N * ‖ξ - η‖ ^ (N + 1)) *
          (‖radianFourierKernel V η‖ * ‖radianFourierKernel f (ξ - η)‖) := by
        convert hh using 1; ring
      _ ≤ (((N + 1 : ℕ) / R) * ‖η‖ * ((3 : ℝ) ^ N * (1 + ‖η‖ ^ N)) *
          ‖ξ - η‖ ^ (N + 1)) *
          (‖radianFourierKernel V η‖ * ‖radianFourierKernel f (ξ - η)‖) := hm
      _ = _ := by
        have hexp : ‖ξ - η‖ ^ (N + 1 : ℝ) = ‖ξ - η‖ ^ (N + 1 : ℕ) := by
          simpa only [Nat.cast_add, Nat.cast_one] using Real.rpow_natCast ‖ξ - η‖ (N + 1)
        simp only [homogeneousCommutatorMoment, homogeneousFourierMagnitude, hexp,
          div_eq_mul_inv, pow_succ]
        ring

theorem homogeneousOrderedCommutator_high_pointwise (N : ℕ)
    (j : Fin (N + 1) → Fin 12) (V f : 𝓢(E, ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hf : ∀ η : E, ‖η‖ < R → radianFourierKernel f η = 0) (ξ : E) :
    ‖radianFourierKernel (homogeneousOrderedCommutator (N + 1) j V f) ξ‖ ≤
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ / R) *
        positiveFrequencyConvolution (homogeneousCommutatorMoment N V)
          (homogeneousFourierMagnitude (N + 1) (radianFourierKernel f)) ξ := by
  let K := homogeneousCommutatorMoment N V
  let g := homogeneousFourierMagnitude (N + 1) (radianFourierKernel f)
  obtain ⟨B, _hB, hB⟩ := homogeneousFourierMagnitude_bounded (N + 1) (by positivity)
    (radianFourierKernel f)
  have hi : Integrable (fun η : E => K η * g (ξ - η)) := by
    apply (homogeneousCommutatorMoment_integrable N V).mul_bdd (c := B)
      ((homogeneousFourierMagnitude_continuous (N + 1) (by positivity)
        (radianFourierKernel f)).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    filter_upwards [] with η
    change ‖homogeneousFourierMagnitude (N + 1) (radianFourierKernel f) (ξ - η)‖ ≤ B
    rw [Real.norm_eq_abs, abs_of_nonneg (homogeneousFourierMagnitude_nonneg _ _ _)]
    exact hB _
  have hb := integral_mono_of_nonneg
    (ae_of_all _ (fun η : E => norm_nonneg
      ((homogeneousOrderedSymbol (N + 1) j ξ - homogeneousOrderedSymbol (N + 1) j (ξ - η)) *
        radianFourierKernel V η * radianFourierKernel f (ξ - η))))
    (hi.const_mul R⁻¹) (ae_of_all _ (commutator_integrand_high N j V f R hR hf ξ))
  rw [integral_const_mul] at hb
  rw [homogeneousOrderedCommutator_fourier, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        ∫ η : E, ‖(homogeneousOrderedSymbol (N + 1) j ξ -
          homogeneousOrderedSymbol (N + 1) j (ξ - η)) *
          radianFourierKernel V η * radianFourierKernel f (ξ - η)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * (R⁻¹ * ∫ η : E, K η * g (ξ - η)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_assoc]; rfl

theorem homogeneousOrderedCommutator_high_energy (N : ℕ)
    (j : Fin (N + 1) → Fin 12) (V f : 𝓢(E, ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hf : ∀ η : E, ‖η‖ < R → radianFourierKernel f η = 0) :
    (∫ ξ : E, ‖radianFourierKernel (homogeneousOrderedCommutator (N + 1) j V f) ξ‖ ^ 2) ≤
      ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ / R) *
        ∫ ξ : E, homogeneousCommutatorMoment N V ξ) ^ 2 *
          homogeneousFrequencyEnergy (N + 1) (radianFourierKernel f) := by
  let c := ((2 * Real.pi) ^ (12 : ℕ))⁻¹ / R
  let K := homogeneousCommutatorMoment N V
  let g := homogeneousFourierMagnitude (N + 1) (radianFourierKernel f)
  obtain ⟨B, hB0, hB⟩ := homogeneousFourierMagnitude_bounded (N + 1) (by positivity)
    (radianFourierKernel f)
  have hY := continuousYoung_nonnegative K g (homogeneousCommutatorMoment_integrable N V)
    (homogeneousFourierMagnitude_continuous (N + 1) (by positivity) _)
    (homogeneousCommutatorMoment_nonneg N V) (homogeneousFourierMagnitude_nonneg _ _)
    (homogeneousFourierMagnitude_sq_integrable (N + 1) (by positivity) _) B hB0 hB
  have hpoint (ξ : E) :
      ‖radianFourierKernel (homogeneousOrderedCommutator (N + 1) j V f) ξ‖ ^ 2 ≤
        c ^ 2 * positiveFrequencyConvolution K g ξ ^ 2 := by
    have hp := pow_le_pow_left₀ (norm_nonneg _)
      (homogeneousOrderedCommutator_high_pointwise N j V f R hR hf ξ) 2
    change _ ≤ (c * positiveFrequencyConvolution K g ξ) ^ 2 at hp
    simpa only [mul_pow] using hp
  have hf2 := ((radianFourierKernel (homogeneousOrderedCommutator (N + 1) j V f)).memLp 2).integrable_norm_pow
    (p := 2) (by norm_num)
  have hi := integral_mono
    hf2 (hY.1.const_mul (c ^ 2)) hpoint
  rw [integral_const_mul] at hi
  have he : (∫ ξ : E, g ξ ^ 2) = homogeneousFrequencyEnergy (N + 1) (radianFourierKernel f) := by
    change (∫ ξ : E, g ξ ^ 2) = ∫ ξ : E,
      ‖ξ‖ ^ (2 * (N + 1 : ℝ)) * ‖radianFourierKernel f ξ‖ ^ 2
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [g, homogeneousFourierMagnitude, mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  calc
    _ ≤ c ^ 2 * ((∫ ξ : E, K ξ) ^ 2 * ∫ ξ : E, g ξ ^ 2) :=
      hi.trans (mul_le_mul_of_nonneg_left hY.2 (sq_nonneg c))
    _ = _ := by rw [he]; dsimp only [c, K]; ring

end DefocusingNLS

end OAI
