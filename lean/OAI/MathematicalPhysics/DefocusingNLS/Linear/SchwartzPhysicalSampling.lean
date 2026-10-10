import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPoissonSummation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzTorusSampling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalLocalization
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierContinuity
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! # The physical function of the uniformly bounded sampled vector

With the exact radian Fourier normalization, the sampled `Y_L` vector is
the periodization of the original physical Schwartz function at period `2πL`.
-/

open scoped SchwartzMap FourierTransform RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def periodizationRescale (L : ℝ) (hL : 0 < L) (ψ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((Units.mk0 (2 * Real.pi * L) (by positivity)) • ContinuousLinearEquiv.refl ℝ E) ψ

theorem periodizationRescale_apply (L : ℝ) (hL : 0 < L) (ψ : 𝓢(E, ℂ)) (x : E) :
    periodizationRescale L hL ψ x = ψ ((2 * Real.pi * L) • x) := by
  simp [periodizationRescale]

theorem fourier_periodizationRescale (L : ℝ) (hL : 0 < L) (ψ : 𝓢(E, ℂ))
    (n : frequencyLattice) :
    𝓕 (periodizationRescale L hL ψ : E → ℂ) (n : E) =
      schwartzLatticeCoefficient L (radianFourierKernel ψ) n := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hd : 0 < 2 * Real.pi * L := by positivity
  have hstd (f : E → ℂ) : radianFourierIntegral f ((2 * Real.pi) • (n : E)) =
      𝓕 f (n : E) := by
    rw [radianFourierIntegral_eq_fourier, smul_smul, inv_mul_cancel₀ hp, one_smul]
  rw [← hstd]
  have hfun : (periodizationRescale L hL ψ : E → ℂ) =
      fun x => ψ (((2 * Real.pi * L)⁻¹)⁻¹ • x) := by
    funext x
    rw [periodizationRescale_apply, inv_inv]
  rw [hfun, radianFourier_dilation (2 * Real.pi * L)⁻¹ (inv_pos.mpr hd)]
  have harg : (2 * Real.pi * L)⁻¹ • ((2 * Real.pi) • (n : E)) = L⁻¹ • (n : E) := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [harg, inv_pow]
  simp only [schwartzLatticeCoefficient, radianFourierKernel_apply, Complex.real_smul]

theorem integerFourierCharacter_rescale (L : ℝ) (_hL : 0 < L)
    (n : frequencyLattice) (y : E) :
    integerFourierCharacter n ((2 * Real.pi * L)⁻¹ • y) =
      spatialFourierCharacter n (L⁻¹ • y) := by
  rw [integerFourierCharacter_exp]
  unfold spatialFourierCharacter
  simp only [real_inner_smul_left]
  congr 1
  push_cast
  field_simp

theorem schwartz_physical_sampling_series (L : ℝ) (hL : 0 < L)
    (ψ : 𝓢(E, ℂ)) (y : E) :
    (∑' n : frequencyLattice, ψ (y + (2 * Real.pi * L) • (n : E))) =
      ∑' n : frequencyLattice, schwartzLatticeCoefficient L (radianFourierKernel ψ) n *
        spatialFourierCharacter n (L⁻¹ • y) := by
  have h := schwartz_poisson_summation (periodizationRescale L hL ψ)
    ((2 * Real.pi * L)⁻¹ • y)
  have hl (n : frequencyLattice) :
      periodizationRescale L hL ψ ((2 * Real.pi * L)⁻¹ • y + (n : E)) =
        ψ (y + (2 * Real.pi * L) • (n : E)) := by
    rw [periodizationRescale_apply, smul_add, smul_smul,
      mul_inv_cancel₀ (show (2 * Real.pi * L : ℝ) ≠ 0 by positivity), one_smul]
  simpa only [hl, fourier_periodizationRescale, integerFourierCharacter_rescale L hL] using h

theorem schwartzTorusSample_physical (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (ψ : 𝓢(E, ℂ)) (y : E) :
    expandingTorusFunction a k L
        (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ))
        (euclideanToTorus (L⁻¹ • y)) =
      ∑' n : frequencyLattice, ψ (y + (2 * Real.pi * L) • (n : E)) := by
  rw [schwartzTorusSample_function a k L ha ha1 hk hL]
  simp only [torusCharacter_euclidean]
  exact (schwartz_physical_sampling_series L (by linarith) ψ y).symm

theorem one_le_norm_frequencyLattice {n : frequencyLattice} (hn : n ≠ 0) : 1 ≤ ‖n‖ := by
  classical
  have hex : ∃ j : Fin 12, frequencyCoordinates n j ≠ 0 := by
    by_contra! h
    apply hn
    apply frequencyCoordinatesEquiv.injective
    rw [map_zero]
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hex
  have hz : (1 : ℝ) ≤ |(frequencyCoordinates n j : ℝ)| := by
    exact_mod_cast Int.one_le_abs hj
  nlinarith [frequencyCoordinates_sq_le n j, sq_abs (frequencyCoordinates n j : ℝ),
    norm_nonneg n]

theorem periodization_eq_of_support_ball (L : ℝ) (hL : 0 < L) (ψ : E → ℂ)
    (hψ : ∀ x : E, 2 * L < ‖x‖ → ψ x = 0) (y : E) (hy : ‖y‖ ≤ L) :
    (∑' n : frequencyLattice, ψ (y + (2 * Real.pi * L) • (n : E))) = ψ y := by
  rw [tsum_eq_single (0 : frequencyLattice)]
  · simp
  · intro n hn
    apply hψ
    have hD : 0 < 2 * Real.pi * L := by positivity
    have hscaled : 2 * Real.pi * L ≤ ‖(2 * Real.pi * L) • (n : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hD, Submodule.norm_coe]
      nlinarith [one_le_norm_frequencyLattice hn]
    have ht : ‖(2 * Real.pi * L) • (n : E)‖ ≤
        ‖y + (2 * Real.pi * L) • (n : E)‖ + ‖y‖ := by
      have h := norm_sub_le (y + (2 * Real.pi * L) • (n : E)) y
      simpa only [add_sub_cancel_left] using h
    nlinarith [mul_pos (sub_pos.mpr Real.pi_gt_three) hL]

theorem schwartzTorusSample_eq_on_ball (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (ψ : 𝓢(E, ℂ)) (hψ : ∀ x : E, 2 * L < ‖x‖ → ψ x = 0)
    (y : E) (hy : ‖y‖ ≤ L) :
    expandingTorusFunction a k L
        (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ))
        (euclideanToTorus (L⁻¹ • y)) = ψ y := by
  rw [schwartzTorusSample_physical a k L ha ha1 hk hL]
  exact periodization_eq_of_support_ball L (by linarith) ψ hψ y hy

end DefocusingNLS

end OAI
