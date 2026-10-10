import OAI.Geometry.RCD.Harmonic.AffineCommutatorIdentity
import OAI.Geometry.RCD.Harmonic.RadialDerivativeNorms
import OAI.Geometry.RCD.Harmonic.RadialLinearRepresentatives

namespace OAI

/-! # The actual affine commutator residual from radial W12 errors -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem normalized_radial_derivative_norm_le (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f q : SobolevSpace μ hQ) {B E : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B ^ 2)
    (hq : (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ q q x ∂μ) ≤ E ^ 2) :
    ‖normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω f hf q)‖ ≤ B * E := by
  have hh := normalized_radial_derivative_norm_sq μ hQ Ω hfin f q hf
  have he := mul_le_mul_of_nonneg_left hq (sq_nonneg B)
  have hs : ‖normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω f hf q)‖ ^ 2 ≤
      (B * E) ^ 2 := by nlinarith only [hh, he]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB hE)).mp hs

/-- All five terms in the exact coefficient identity are controlled by
the two actual W12 fits and the full-mass commutator error. -/
theorem normalized_affine_commutator_bound {n : ℕ}
    (Ω : Set X) (hfin : μ Ω ≠ ∞) (f v η : SobolevSpace μ hQ)
    {Cf Cv eg dg eh dh k : ℝ}
    (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv) (hdg : 0 ≤ dg) (hdh : 0 ≤ dh)
    (heg : 0 ≤ eg) (heh : 0 ≤ eh)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ Cf ^ 2)
    (hv : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ v v x ≤ Cv ^ 2)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (U G H : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (hG : ∀ a, SobolevSpace.toLp μ hQ (G a) =ᵐ[μ.restrict Ω] localGamma μ hQ f (U a))
    (hH : ∀ a, SobolevSpace.toLp μ hQ (H a) =ᵐ[μ.restrict Ω] localGamma μ hQ v (U a))
    (A B : Euclidean n →L[ℝ] Euclidean n) (c : Euclidean n →L[ℝ] ℝ)
    (hgv : ∀ a, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (G a - U (A a)))‖ ≤ eg * ‖a‖)
    (hge : ∀ a, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ
      (G a - U (A a)) (G a - U (A a)) x ∂μ) ≤ (dg * ‖a‖) ^ 2)
    (hhv : ∀ a, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (H a - U (B a) - c a • η))‖ ≤ eh * ‖a‖)
    (hhe : ∀ a, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ
      (H a - U (B a) - c a • η) (H a - U (B a) - c a • η) x ∂μ) ≤ (dh * ‖a‖) ^ 2)
    (hcomm : ∀ a, ‖normalizeLocalL2 μ Ω hfin
      (localRadialDerivative μ hQ Ω v hv (G a) -
        localRadialDerivative μ hQ Ω f hf (H a) - SobolevSpace.restrictLp μ hQ Ω (H a))‖ ≤ k * ‖a‖)
    (b : Euclidean n) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (U ((A * B - B * (A - 1)) b) - c ((A - 1) b) • η))‖ ≤
      (Cv * dg + k + Cf * dh + eh * ‖A - 1‖ + eg * ‖B‖) * ‖b‖ := by
  let Z : Lp ℝ 2 (μ.restrict Ω) →ₗ[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
    ‖restrictedOne μ Ω hfin‖⁻¹ • LinearMap.id
  let D := Z.comp (localRadialDerivative μ hQ Ω f hf)
  let V := Z.comp (localRadialDerivative μ hQ Ω v hv)
  let J := Z.comp (SobolevSpace.restrictLp μ hQ Ω).toLinearMap
  let C : Euclidean n →ₗ[ℝ] SobolevSpace μ hQ := c.toLinearMap.smulRight η
  have hDU (a) : D (U a) = J (G a) := by
    dsimp only [D, J, LinearMap.comp_apply]
    rw [localRadialDerivative_eq_restrict μ hQ Ω f (U a) (G a) hf (hG a)]
    rfl
  have hVU (a) : V (U a) = J (H a) := by
    dsimp only [V, J, LinearMap.comp_apply]
    rw [localRadialDerivative_eq_restrict μ hQ Ω v (U a) (H a) hv (hH a)]
    rfl
  have hDC (a) : D (C a) = 0 := by
    change Z (localRadialDerivative μ hQ Ω f hf (c a • η)) = 0
    rw [map_smul, localRadialDerivative_constant μ hQ Ω f η hf 1 hη, smul_zero, map_zero]
  have h₁ : ‖V (G b - U (A b))‖ ≤ Cv * dg * ‖b‖ := by
    exact (normalized_radial_derivative_norm_le μ hQ Ω hfin v _ hCv
      (mul_nonneg hdg (norm_nonneg b)) hv (hge b)).trans_eq (by ring)
  have h₃ : ‖D (H b - U (B b) - C b)‖ ≤ Cf * dh * ‖b‖ := by
    exact (normalized_radial_derivative_norm_le μ hQ Ω hfin f _ hCf
      (mul_nonneg hdh (norm_nonneg b)) hf (hhe b)).trans_eq (by ring)
  have h₄ : ‖J (H ((A - 1) b) - U (B ((A - 1) b)) - C ((A - 1) b))‖ ≤
      eh * ‖A - 1‖ * ‖b‖ := by
    exact (hhv ((A - 1) b)).trans ((mul_le_mul_of_nonneg_left
      ((A - 1).le_opNorm b) heh).trans_eq (by ring))
  have h₅ : ‖J (G (B b) - U (A (B b)))‖ ≤ eg * ‖B‖ * ‖b‖ := by
    exact (hgv (B b)).trans ((mul_le_mul_of_nonneg_left (B.le_opNorm b) heg).trans_eq (by ring))
  have h₂ : ‖V (G b) - D (H b) - J (H b)‖ ≤ k * ‖b‖ := by
    change ‖normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω v hv (G b)) -
      normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω f hf (H b)) -
      normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (H b))‖ ≤ _
    simpa only [normalizeLocalL2, smul_sub] using hcomm b
  have hh := affine_commutator_error_bound A.toLinearMap B.toLinearMap
    U.toLinearMap G.toLinearMap H.toLinearMap C D V J hDU hVU hDC b h₁ h₂ h₃ h₄ h₅
  change ‖J (U ((A * B - B * (A - 1)) b)) - J (C ((A - 1) b))‖ ≤ _ at hh
  rw [← map_sub] at hh
  exact hh.trans_eq (by ring)

end RegularPointCoordinates

end

end OAI
