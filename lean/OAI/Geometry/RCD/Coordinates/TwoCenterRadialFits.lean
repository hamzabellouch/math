import OAI.Geometry.RCD.Sobolev.LocalAffineCutoff

namespace OAI

/-! # Subtracting the two actual radial fits in their common frame -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Local energy obeys the squared triangle estimate on an arbitrary
common region, retaining its original normalization. -/
theorem averaged_energy_sub_le (Ω : Set X) (f g : SobolevSpace μ hQ) :
    (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ (f - g) (f - g) x ∂μ) ≤
      2 * ((μ.real Ω)⁻¹ * ∫ x in Ω, localGamma μ hQ f f x ∂μ) +
      2 * ((μ.real Ω)⁻¹ * ∫ x in Ω, localGamma μ hQ g g x ∂μ) := by
  have hp : ∀ᵐ x ∂μ, localGamma μ hQ (f - g) (f - g) x ≤
      2 * localGamma μ hQ f f x + 2 * localGamma μ hQ g g x := by
    have hn (q : SobolevSpace μ hQ) : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.minimalSlope μ hQ q x :=
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ q)
    filter_upwards [(Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_sub_le μ hQ f g),
      Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ f) (SobolevSpace.minimalSlope μ hQ g),
      hn f, hn g, hn (f - g), localGamma_self μ hQ f, localGamma_self μ hQ g,
      localGamma_self μ hQ (f - g)] with x hs ha hf hg hfg hff hgg hsub
    simp only [ha, Pi.add_apply] at hs
    rw [hff, hgg, hsub]
    have hsq := (sq_le_sq₀ hfg (add_nonneg hf hg)).mpr hs
    nlinarith only [hsq, sq_nonneg (SobolevSpace.minimalSlope μ hQ f x -
      SobolevSpace.minimalSlope μ hQ g x)]
  have hi := integral_mono_ae (μ := μ.restrict Ω)
    (localGamma_memL1 μ hQ (f - g) (f - g)).integrableOn
    (((localGamma_memL1 μ hQ f f).integrableOn.const_mul 2).add
      ((localGamma_memL1 μ hQ g g).integrableOn.const_mul 2)) (ae_restrict_of_ae hp)
  simp only [Pi.add_apply] at hi
  rw [integral_add ((localGamma_memL1 μ hQ f f).integrableOn.const_mul 2)
      ((localGamma_memL1 μ hQ g g).integrableOn.const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ (μ.real Ω)⁻¹ by positivity)
  convert hh using 1
  ring

omit [BorelSpace X] [ProperSpace X] in
theorem normalized_sobolev_sub_sq_le (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f g : SobolevSpace μ hQ) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (f - g))‖ ^ 2 ≤
      2 * ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω f)‖ ^ 2 +
      2 * ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω g)‖ ^ 2 := by
  let a := normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω f)
  let b := normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω g)
  have he : normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (f - g)) = a - b := by
    simp only [a, b, map_sub, normalizeLocalL2, smul_sub]
  rw [he]
  have hs := (sq_le_sq₀ (norm_nonneg (a - b))
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (norm_sub_le a b)
  change ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2
  nlinarith only [hs, sq_nonneg (‖a‖ - ‖b‖)]

/-- The difference of the two radial representatives represents the
derivative of the difference of the two actual Poisson replacements. -/
theorem radial_difference_representative (Ω : Set X)
    (fz fx u gz gx : SobolevSpace μ hQ)
    (hz : SobolevSpace.toLp μ hQ gz =ᵐ[μ.restrict Ω] localGamma μ hQ fz u)
    (hx : SobolevSpace.toLp μ hQ gx =ᵐ[μ.restrict Ω] localGamma μ hQ fx u) :
    SobolevSpace.toLp μ hQ (gz - gx) =ᵐ[μ.restrict Ω] localGamma μ hQ (fz - fx) u := by
  change SobolevSpace.toLpCLM μ hQ (gz - gx) =ᵐ[μ.restrict Ω] _
  rw [map_sub]
  change (SobolevSpace.toLp μ hQ gz - SobolevSpace.toLp μ hQ gx) =ᵐ[μ.restrict Ω] _
  filter_upwards [hz, hx, ae_restrict_of_ae (localGamma_sub_left μ hQ fz fx u),
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ gz) (SobolevSpace.toLp μ hQ gx))]
    with x hz hx hg hs
  simp only [hs, Pi.sub_apply, hz, hx, hg]

/-- Subtracting the common-frame fits produces the affine fit of the
two-center derivative, with the original displacement constant. -/
theorem two_center_radial_fit_bounds {n : ℕ}
    (Ω : Set X) (hfin : μ Ω ≠ ∞) (η : SobolevSpace μ hQ)
    (U Gz Gx : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (Az Ax : Euclidean n →L[ℝ] Euclidean n) (c : Euclidean n →L[ℝ] ℝ)
    {Ez Ex Dz Dx : ℝ}
    (hzv : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (Gz b - U (Az b)))‖ ^ 2 ≤ Ez * ‖b‖ ^ 2)
    (hxv : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (Gx b - U (Ax b) + c b • η))‖ ^ 2 ≤ Ex * ‖b‖ ^ 2)
    (hze : ∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ
      (Gz b - U (Az b)) (Gz b - U (Az b)) x ∂μ) ≤ Dz * ‖b‖ ^ 2)
    (hxe : ∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ
      (Gx b - U (Ax b) + c b • η) (Gx b - U (Ax b) + c b • η) x ∂μ) ≤ Dx * ‖b‖ ^ 2)
    (b : Euclidean n) :
    let R := (Gz - Gx) b - U ((Az - Ax) b) - c b • η
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω R)‖ ^ 2 ≤
      (2 * Ez + 2 * Ex) * ‖b‖ ^ 2 ∧
    (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hQ R R x ∂μ) ≤
      (2 * Dz + 2 * Dx) * ‖b‖ ^ 2 := by
  have he : (Gz - Gx) b - U ((Az - Ax) b) - c b • η =
      (Gz b - U (Az b)) - (Gx b - U (Ax b) + c b • η) := by
    simp only [sub_apply, map_sub]
    module
  dsimp only
  rw [he]
  have hv := normalized_sobolev_sub_sq_le μ hQ Ω hfin
    (Gz b - U (Az b)) (Gx b - U (Ax b) + c b • η)
  have hh := averaged_energy_sub_le μ hQ Ω
    (Gz b - U (Az b)) (Gx b - U (Ax b) + c b • η)
  constructor
  · nlinarith only [hv, hzv b, hxv b]
  · nlinarith only [hh, hze b, hxe b]

end RegularPointCoordinates

end

end OAI
