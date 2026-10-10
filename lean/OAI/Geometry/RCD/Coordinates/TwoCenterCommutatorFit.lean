import OAI.Geometry.RCD.Coordinates.TwoCenterRadialFits
import OAI.Geometry.RCD.Harmonic.AffineCommutatorResidual

namespace OAI

/-! # The commutator coefficient residual from the two radial W12 fits -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

theorem norm_le_sqrt_mul_of_sq_le {Y : Type*} [SeminormedAddCommGroup Y]
    (y : Y) {E r : ℝ} (hE : 0 ≤ E) (hr : 0 ≤ r) (h : ‖y‖ ^ 2 ≤ E * r ^ 2) :
    ‖y‖ ≤ Real.sqrt E * r := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)).mp
  rwa [mul_pow, Real.sq_sqrt hE]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A normalized integral commutator bound is precisely the L2 error
required by the affine coefficient identity, for the chosen representatives. -/
theorem normalized_commutator_fit_norm (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f v u g h : SobolevSpace μ hQ) {Cf Cv E r : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ Cf)
    (hv : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ v v x ≤ Cv)
    (hh : SobolevSpace.toLp μ hQ h =ᵐ[μ.restrict Ω] localGamma μ hQ v u)
    (hE : 0 ≤ E) (hr : 0 ≤ r)
    (he : (μ.real Ω)⁻¹ * (∫ x in Ω,
      (localGamma μ hQ v g x - localGamma μ hQ f h x - localGamma μ hQ v u x) ^ 2 ∂μ) ≤ E * r ^ 2) :
    ‖normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω v hv g -
      localRadialDerivative μ hQ Ω f hf h - SobolevSpace.restrictLp μ hQ Ω h)‖ ≤ Real.sqrt E * r := by
  apply norm_le_sqrt_mul_of_sq_le _ hE hr
  rw [normalizeLocalL2_norm_sq, ← l2_norm_sq_eq_integral,
    local_radial_commutator_norm_sq μ hQ Ω f v u g h hf hv hh]
  exact he

/-- This is the quantitative affine residual of the actual two-center
argument. Its hypotheses are the two radial fits and the separately proved
full Poisson-mass commutator estimate, all on the same region. -/
theorem two_center_affine_commutator_bound {n : ℕ}
    (Ω : Set X) (hfin : μ Ω ≠ ∞) (fz fx η : SobolevSpace μ hQ)
    {Cf Cv Ez Ex Dz Dx K : ℝ}
    (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hEz : 0 ≤ Ez) (hEx : 0 ≤ Ex) (hDz : 0 ≤ Dz) (hDx : 0 ≤ Dx) (hK : 0 ≤ K)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ fz fz x ≤ Cf ^ 2)
    (hv : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ (fz - fx) (fz - fx) x ≤ Cv ^ 2)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (U Gz Gx : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (hGz : ∀ a, SobolevSpace.toLp μ hQ (Gz a) =ᵐ[μ.restrict Ω] localGamma μ hQ fz (U a))
    (hGx : ∀ a, SobolevSpace.toLp μ hQ (Gx a) =ᵐ[μ.restrict Ω] localGamma μ hQ fx (U a))
    (Az Ax : Euclidean n →L[ℝ] Euclidean n) (c : Euclidean n →L[ℝ] ℝ)
    (hzv : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (Gz b - U (Az b)))‖ ^ 2 ≤ Ez * ‖b‖ ^ 2)
    (hxv : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (Gx b - U (Ax b) + c b • η))‖ ^ 2 ≤ Ex * ‖b‖ ^ 2)
    (hze : ∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ
      (Gz b - U (Az b)) (Gz b - U (Az b)) x ∂μ) ≤ Dz * ‖b‖ ^ 2)
    (hxe : ∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ
      (Gx b - U (Ax b) + c b • η) (Gx b - U (Ax b) + c b • η) x ∂μ) ≤ Dx * ‖b‖ ^ 2)
    (hcomm : ∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω,
      (localGamma μ hQ (fz - fx) (Gz b) x - localGamma μ hQ fz ((Gz - Gx) b) x -
        localGamma μ hQ (fz - fx) (U b) x) ^ 2 ∂μ) ≤ K * ‖b‖ ^ 2)
    (b : Euclidean n) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (U ((Az * (Az - Ax) - (Az - Ax) * (Az - 1)) b) - c ((Az - 1) b) • η))‖ ≤
      (Cv * Real.sqrt Dz + Real.sqrt K + Cf * Real.sqrt (2 * Dz + 2 * Dx) +
        Real.sqrt (2 * Ez + 2 * Ex) * ‖Az - 1‖ + Real.sqrt Ez * ‖Az - Ax‖) * ‖b‖ := by
  have hE : 0 ≤ 2 * Ez + 2 * Ex := by positivity
  have hD : 0 ≤ 2 * Dz + 2 * Dx := by positivity
  have hH (a) : SobolevSpace.toLp μ hQ ((Gz - Gx) a) =ᵐ[μ.restrict Ω]
      localGamma μ hQ (fz - fx) (U a) :=
    radial_difference_representative μ hQ Ω fz fx (U a) (Gz a) (Gx a) (hGz a) (hGx a)
  have hpair (a) := two_center_radial_fit_bounds μ hQ Ω hfin η U Gz Gx Az Ax c hzv hxv hze hxe a
  apply normalized_affine_commutator_bound μ hQ Ω hfin fz (fz - fx) η hCf hCv
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hf hv hη U Gz (Gz - Gx) hGz hH Az (Az - Ax) c
  · intro a
    exact norm_le_sqrt_mul_of_sq_le _ hEz (norm_nonneg a) (hzv a)
  · intro a
    simpa only [mul_pow, Real.sq_sqrt hDz] using hze a
  · intro a
    exact norm_le_sqrt_mul_of_sq_le _ hE (norm_nonneg a) (hpair a).1
  · intro a
    simpa only [mul_pow, Real.sq_sqrt hD] using (hpair a).2
  · intro a
    exact normalized_commutator_fit_norm μ hQ Ω hfin fz (fz - fx) (U a)
      (Gz a) ((Gz - Gx) a) hf hv (hH a) hK (norm_nonneg a) (hcomm a)

end RegularPointCoordinates

end

end OAI
