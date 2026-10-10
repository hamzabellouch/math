import OAI.Geometry.RCD.Coordinates.LinearRadialFits
import OAI.Geometry.RCD.Coordinates.FramedPointValues
import OAI.Geometry.RCD.Harmonic.RadialLinearRepresentatives

namespace OAI

/-! # The actual row fits in the centered normalized projection coordinates -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Only the scalar value fits are needed to build the radial operator
used in sharp projection. -/
theorem centered_normalized_radial_values {n : ℕ}
    (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (u g : Fin n → SobolevSpace μ hQ) (f eta : SobolevSpace μ hQ)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (z : Euclidean n)
    (coeff : Fin n → Euclidean n) {E B : ℝ} (hE : 0 ≤ E)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (g j) =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (transformedColumn μ hQ u N j))
    (hvalue : ∀ j, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (g j - centeredAffineSobolev μ hQ u eta z (coeff j)))‖ ^ 2 ≤ E) :
    let uc := centeredColumn μ hQ (transformedColumn μ hQ u N)
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) eta
    let G := sobolevColumnMap μ hQ g
    let A := N.symm.toContinuousLinearMap.comp (finiteCoefficientMap coeff)
    (∀ b, SobolevSpace.toLp μ hQ (G b) =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (sobolevColumnMap μ hQ uc b)) ∧
    (∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (G b - sobolevColumnMap μ hQ uc (A b)))‖ ^ 2 ≤ (n : ℝ) ^ 2 * E * ‖b‖ ^ 2) := by
  dsimp only
  let uc := centeredColumn μ hQ (transformedColumn μ hQ u N)
    ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) eta
  let A := N.symm.toContinuousLinearMap.comp (finiteCoefficientMap coeff)
  have hfit (b : Euclidean n) : sobolevColumnMap μ hQ uc (A b) =
      centeredAffineSobolev μ hQ u eta z (finiteCoefficientMap coeff b) := by
    apply centered_frame_covector_eq μ hQ u N eta z
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) (finiteCoefficientMap coeff b)
    have hh := ContinuousLinearMap.adjoint_inner_left
      (N : Euclidean n →L[ℝ] Euclidean n) (N.symm (finiteCoefficientMap coeff b)) z
    simpa only [ContinuousLinearEquiv.coe_coe, N.apply_symm_apply] using hh
  refine ⟨?_, ?_⟩
  · intro b
    have hd := localRadialDerivative_column μ hQ Ω f hf (transformedColumn μ hQ u N) g hrep b
    have hc := localRadialDerivative_eq_of_constant_difference μ hQ Ω f
      (sobolevColumnMap μ hQ uc b) (sobolevColumnMap μ hQ (transformedColumn μ hQ u N) b) hf _
      (centeredColumn_covector_difference μ hQ (transformedColumn μ hQ u N) Ω
        ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) b eta heta)
    have hr := localRadialDerivative_representative μ hQ Ω f (sobolevColumnMap μ hQ uc b) hf
    rw [hc, hd] at hr
    exact (SobolevSpace.restrictLp_coe μ hQ Ω _).symm.trans hr
  · intro b
    rw [hfit b, ← centered_radial_residual_column μ hQ]
    exact normalized_column_sq_le μ hQ _ Ω hfin hE hvalue b

/-- The dyadic row fits provide one genuine radial derivative operator
and one coefficient operator in the centered normalized coordinates.
The same residual controls values and energy for every covector. -/
theorem centered_normalized_radial_rows {n : ℕ}
    (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (u g : Fin n → SobolevSpace μ hQ) (f eta : SobolevSpace μ hQ)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (z : Euclidean n)
    (coeff : Fin n → Euclidean n) {E D B : ℝ} (hE : 0 ≤ E) (_hD : 0 ≤ D)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (g j) =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (transformedColumn μ hQ u N j))
    (hvalue : ∀ j, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (g j - centeredAffineSobolev μ hQ u eta z (coeff j)))‖ ^ 2 ≤ E)
    (henergy : ∀ j, (μ.real Ω)⁻¹ * ∫ x in Ω,
      localGamma μ hQ (g j - centeredAffineSobolev μ hQ u eta z (coeff j))
        (g j - centeredAffineSobolev μ hQ u eta z (coeff j)) x ∂μ ≤ D) :
    let uc := centeredColumn μ hQ (transformedColumn μ hQ u N)
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) eta
    let G := sobolevColumnMap μ hQ g
    let A := N.symm.toContinuousLinearMap.comp (finiteCoefficientMap coeff)
    (∀ b, SobolevSpace.toLp μ hQ (G b) =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (sobolevColumnMap μ hQ uc b)) ∧
    (∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (G b - sobolevColumnMap μ hQ uc (A b)))‖ ^ 2 ≤ (n : ℝ) ^ 2 * E * ‖b‖ ^ 2) ∧
    (∀ b, (μ.real Ω)⁻¹ * ∫ x in Ω,
      localGamma μ hQ (G b - sobolevColumnMap μ hQ uc (A b))
        (G b - sobolevColumnMap μ hQ uc (A b)) x ∂μ ≤ (n : ℝ) ^ 2 * D * ‖b‖ ^ 2) := by
  dsimp only
  let uc := centeredColumn μ hQ (transformedColumn μ hQ u N)
    ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) eta
  let A := N.symm.toContinuousLinearMap.comp (finiteCoefficientMap coeff)
  have hfit (b : Euclidean n) : sobolevColumnMap μ hQ uc (A b) =
      centeredAffineSobolev μ hQ u eta z (finiteCoefficientMap coeff b) := by
    apply centered_frame_covector_eq μ hQ u N eta z
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) (finiteCoefficientMap coeff b)
    have hh := ContinuousLinearMap.adjoint_inner_left
      (N : Euclidean n →L[ℝ] Euclidean n) (N.symm (finiteCoefficientMap coeff b)) z
    simpa only [ContinuousLinearEquiv.coe_coe, N.apply_symm_apply] using hh
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hd := localRadialDerivative_column μ hQ Ω f hf (transformedColumn μ hQ u N) g hrep b
    have hconst := centeredColumn_covector_difference μ hQ (transformedColumn μ hQ u N) Ω
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) b eta heta
    have hc := localRadialDerivative_eq_of_constant_difference μ hQ Ω f
      (sobolevColumnMap μ hQ uc b) (sobolevColumnMap μ hQ (transformedColumn μ hQ u N) b) hf _ hconst
    have hr := localRadialDerivative_representative μ hQ Ω f (sobolevColumnMap μ hQ uc b) hf
    rw [hc, hd] at hr
    exact (SobolevSpace.restrictLp_coe μ hQ Ω _).symm.trans hr
  · intro b
    rw [hfit b, ← centered_radial_residual_column μ hQ]
    exact normalized_column_sq_le μ hQ _ Ω hfin hE hvalue b
  · intro b
    rw [hfit b, ← centered_radial_residual_column μ hQ]
    exact weighted_column_energy_bound μ hQ _ Ω (by positivity) henergy b

end RegularPointCoordinates

end

end OAI
