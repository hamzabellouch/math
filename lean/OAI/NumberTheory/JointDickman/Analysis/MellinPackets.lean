import OAI.NumberTheory.JointDickman.Amplification.SchwartzFourierProfile

namespace OAI

/-! # Smoothed logarithmic windows and their Dirichlet energy

A finite sum of translates of a Schwartz window is itself Schwartz. Its
Fourier transform factors into the window transform and the actual finite
Dirichlet polynomial. Plancherel therefore identifies the two energies
without a truncation or an arithmetic hypothesis.
-/
namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap FourierTransform

/-- The reciprocal-weighted Dirichlet polynomial in Fourier normalization. -/
noncomputable def mellinPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (ξ : ℝ) : ℂ :=
  ∑ n ∈ S, (a n / (n : ℂ)) * additivePhase (-ξ * Real.log (n : ℝ))

/-- A smoothed logarithmic window, retaining the literal coefficients. -/
noncomputable def mellinPacket (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) :
    𝓢(ℝ, ℂ) :=
  ∑ n ∈ S, (a n / (n : ℂ)) • w.compSubConstCLM ℂ (Real.log (n : ℝ))

theorem mellinPacket_apply (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) (v : ℝ) :
    mellinPacket S a w v =
      ∑ n ∈ S, (a n / (n : ℂ)) * w (v - Real.log (n : ℝ)) := by
  simp [mellinPacket, smul_eq_mul]

theorem fourier_schwartz_translate (w : 𝓢(ℝ, ℂ)) (u ξ : ℝ) :
    (𝓕 (w.compSubConstCLM ℂ u) : 𝓢(ℝ, ℂ)) ξ =
      additivePhase (-ξ * u) * (𝓕 w : 𝓢(ℝ, ℂ)) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  change (∫ v : ℝ, Real.fourierChar (-(v * ξ)) • w (v - u)) = _
  rw [← integral_add_right_eq_self (fun v : ℝ =>
    Real.fourierChar (-(v * ξ)) • w (v - u)) u]
  simp only [add_sub_cancel_right]
  have hphase (v : ℝ) : Real.fourierChar (-((v + u) * ξ)) =
      Real.fourierChar (-(u * ξ)) * Real.fourierChar (-(v * ξ)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hphase, Circle.smul_def, Circle.coe_mul, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  have he : (Real.fourierChar (-(u * ξ)) : ℂ) = additivePhase (-ξ * u) := by
    simp only [Real.fourierChar_apply, additivePhase]
    congr 1
    push_cast
    ring
  simp only [Circle.smul_def, he, smul_eq_mul]

theorem mellinPacket_fourier (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (mellinPacket S a w) : 𝓢(ℝ, ℂ)) ξ =
      (𝓕 w : 𝓢(ℝ, ℂ)) ξ * mellinPolynomial S a ξ := by
  change (SchwartzMap.fourierTransformCLM ℂ (mellinPacket S a w)) ξ = _
  simp only [mellinPacket, map_sum, map_smul, SchwartzMap.fourierTransformCLM_apply,
    _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    fourier_schwartz_translate, mellinPolynomial, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

/-- Exact Plancherel transfer for the smoothed logarithmic window. -/
theorem mellinPacket_energy (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) :
    (∫ v : ℝ, ‖mellinPacket S a w v‖ ^ 2) =
      ∫ ξ : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 * ‖mellinPolynomial S a ξ‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier (mellinPacket S a w)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp only
    rw [mellinPacket_fourier, norm_mul, mul_pow])

end JointDickman

end OAI
