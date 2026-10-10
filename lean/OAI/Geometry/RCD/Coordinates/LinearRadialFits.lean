import OAI.Geometry.RCD.Sobolev.FiniteColumnEnergy
import OAI.Geometry.RCD.Sobolev.CenteredAffineSobolev
import OAI.Geometry.RCD.Harmonic.CenteredColumns

namespace OAI

/-! # Linear assembly of the actual centered radial fits -/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

/-- The original affine coefficients, extended linearly from basis rows. -/
def finiteCoefficientMap {n : ℕ} (coeff : Fin n → Euclidean n) :
    Euclidean n →L[ℝ] Euclidean n :=
  ∑ j, (EuclideanSpace.proj j).smulRight (coeff j)

theorem finiteCoefficientMap_apply {n : ℕ} (coeff : Fin n → Euclidean n) (b : Euclidean n) :
    finiteCoefficientMap coeff b = ∑ j, b j • coeff j := by
  simp [finiteCoefficientMap]

theorem finiteCoefficientMap_single {n : ℕ} (coeff : Fin n → Euclidean n) (j : Fin n) :
    finiteCoefficientMap coeff (EuclideanSpace.single j 1) = coeff j := by
  classical
  simp [finiteCoefficientMap_apply, PiLp.single_apply]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Centering preserves the linear dependence on the affine covector. -/
def centeredSobolevMap {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (η : SobolevSpace μ hQ) (v : Euclidean n) : Euclidean n →L[ℝ] SobolevSpace μ hQ :=
  sobolevColumnMap μ hQ u - (innerSL ℝ v).smulRight η

omit [BorelSpace X] [ProperSpace X] in
theorem centeredSobolevMap_apply {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (η : SobolevSpace μ hQ) (v a : Euclidean n) :
    centeredSobolevMap μ hQ u η v a = centeredAffineSobolev μ hQ u η v a := by
  change sobolevColumnMap μ hQ u a - ⟪v, a⟫_ℝ • η =
    (-⟪v, a⟫_ℝ) • η + sobolevColumnMap μ hQ u a
  module

omit [BorelSpace X] [ProperSpace X] in
/-- Combining centered row fits is exactly the centered fit with the
combined coefficient, so the value and gradient estimates use one residual. -/
theorem centered_radial_residual_column {n : ℕ}
    (u g : Fin n → SobolevSpace μ hQ) (η : SobolevSpace μ hQ) (v : Euclidean n)
    (coeff : Fin n → Euclidean n) (b : Euclidean n) :
    sobolevColumnMap μ hQ (fun j => g j - centeredAffineSobolev μ hQ u η v (coeff j)) b =
      sobolevColumnMap μ hQ g b - centeredAffineSobolev μ hQ u η v (finiteCoefficientMap coeff b) := by
  let R := sobolevColumnMap μ hQ g - (centeredSobolevMap μ hQ u η v).comp (finiteCoefficientMap coeff)
  have hrow : (fun j => g j - centeredAffineSobolev μ hQ u η v (coeff j)) =
      (fun j => R (EuclideanSpace.single j 1)) := by
    funext j
    simp only [R, sub_apply, ContinuousLinearMap.comp_apply,
      sobolevColumnMap_single, finiteCoefficientMap_single, centeredSobolevMap_apply]
  rw [hrow, sobolevColumnMap_of_linear]
  simp only [R, sub_apply, ContinuousLinearMap.comp_apply, centeredSobolevMap_apply]

/-- All rowwise W12 bounds from the actual dyadic radial construction
extend to every covector with the same combined affine coefficient. -/
theorem linear_centered_radial_bounds {n : ℕ}
    (u g : Fin n → SobolevSpace μ hQ) (η : SobolevSpace μ hQ) (v : Euclidean n)
    (coeff : Fin n → Euclidean n) (Ω Ω' : Set X) (hfin : μ Ω ≠ ∞) {E D : ℝ} (hE : 0 ≤ E)
    (hvalue : ∀ j, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (g j - centeredAffineSobolev μ hQ u η v (coeff j)))‖ ^ 2 ≤ E)
    (henergy : ∀ j, (∫ x in Ω', localGamma μ hQ
      (g j - centeredAffineSobolev μ hQ u η v (coeff j))
      (g j - centeredAffineSobolev μ hQ u η v (coeff j)) x ∂μ) ≤ D)
    (b : Euclidean n) :
    let R := sobolevColumnMap μ hQ g b - centeredAffineSobolev μ hQ u η v (finiteCoefficientMap coeff b)
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω R)‖ ^ 2 ≤ (n : ℝ) ^ 2 * E * ‖b‖ ^ 2 ∧
    (∫ x in Ω', localGamma μ hQ R R x ∂μ) ≤ (n : ℝ) ^ 2 * D * ‖b‖ ^ 2 := by
  dsimp only
  constructor
  · have hh := normalized_column_sq_le μ hQ
      (fun j => g j - centeredAffineSobolev μ hQ u η v (coeff j)) Ω hfin hE hvalue b
    rwa [centered_radial_residual_column μ hQ] at hh
  · have hh := column_energy_bound μ hQ
      (fun j => g j - centeredAffineSobolev μ hQ u η v (coeff j)) Ω' henergy b
    rwa [centered_radial_residual_column μ hQ] at hh

end RegularPointCoordinates

end

end OAI
