import OAI.Geometry.RCD.Harmonic.ActualProjectionConfiguration
import OAI.Geometry.RCD.Coordinates.ProjectionAffineNormalization
import OAI.Geometry.RCD.Coordinates.ProjectionCoordinateValues
import OAI.Geometry.RCD.Coordinates.LinearRadialFits
import OAI.Geometry.RCD.Harmonic.RadialLinearRepresentatives

namespace OAI

/-! # Constructing the actual projection data from normalized coordinates -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Exact normalized, centered harmonic coordinates and the actual scalar
row fits construct the sharp-projection configuration. The affine constant
is chosen before the centers, scales, sources, and coordinate map. -/
theorem normalized_projection_configuration {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {κ B J C A Cχ epsilon Drow : ℝ} (hκ : 0 ≤ κ) (hepsilon : 0 ≤ epsilon)
    (hDrow : 0 ≤ Drow)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (16384 : ℝ) ^ n) * epsilon) ≤ 1 / 2) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (root : ℝ) (first center : X)
      (S1 : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ first root)
      (S2 : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ center root)
      (T1 : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S1 B J C)
      (T2 : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S2 B J C) (i : ℕ),
      let s := distanceSourceRadius root i
      root ≤ 1 → dist center first ≤ s / 4 → -1 ≤ K * s ^ 2 →
      -κ ≤ K * (s / 512) ^ 2 →
      (n : ℝ) + κ * (4 * s) ^ 2 ≤ (n : ℝ) + 1 →
      (∀ t : ℝ, 0 < t → t ≤ root →
        |(hausdorff n X).real (ball center t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4) →
      (hausdorff n X) (sphere center (s / 2048)) = 0 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (V : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic center (2 * s) epsilon u V →
      sobolevMeanGram (hausdorff n X) hX.quadratic (sobolevColumnMap (hausdorff n X) hX.quadratic u)
        (ball center (2 * s)) measurableSet_ball = ContinuousLinearMap.id ℝ (Euclidean n) →
      V center = 0 →
      ∀ delta : ℝ, delta ≤ 1 →
      IsPointedApproximation center 0 (s / 64) 4 delta (fun x => (s / 64)⁻¹ • V x) →
      ∀ error : ℝ, 0 < error →
      IsMeasuredEuclideanApproximation (hausdorff n X) n center s (1 / 1024) error
        (fun x => s⁻¹ • V x) →
      ∀ one : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic one =ᵐ[
        (hausdorff n X).restrict (ball center (2 * s))] fun _ => (1 : ℝ)) →
      ∀ _cutoff : GoodLaplacianCutoff (hausdorff n X) hX.quadratic center (s / 64) Cχ,
      (∀ᵐ x ∂(hausdorff n X).restrict (ball center (s / 4)),
        localGamma (hausdorff n X) hX.quadratic (T1.replacement i) (T1.replacement i) x ≤ (A * s) ^ 2) →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball center (s / 4)),
        localGamma (hausdorff n X) hX.quadratic (T2.replacement i) (T2.replacement i) x ≤ (A * s) ^ 2) →
      ∀ source : ℝ, 0 < source →
      normalizedPoissonDefect (hausdorff n X) hX.quadratic S1 i +
        normalizedPoissonDefect (hausdorff n X) hX.quadratic S2 i ≤ source ^ 2 →
      ∀ (g : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (coeff : Fin n → Euclidean n),
      (∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (g j) =ᵐ[
        (hausdorff n X).restrict (ball center (s / 512))]
        localGamma (hausdorff n X) hX.quadratic (T2.replacement i) (u j)) →
      (∀ j, ‖normalizeLocalL2 (hausdorff n X) (ball center (s / 512))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball center (s / 512))
          (g j - sobolevColumnMap (hausdorff n X) hX.quadratic u (coeff j)))‖ ^ 2 ≤
            Drow * s ^ 2 * source ^ 2) →
      ∀ total : ℝ, 0 ≤ total →
      Summable (normalizedPoissonDefect (hausdorff n X) hX.quadratic S2) →
      (∑' j, normalizedPoissonDefect (hausdorff n X) hX.quadratic S2 j) ≤ total →
      ∃ d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H
        ((n : ℝ) * Real.sqrt Drow) 1 1,
        d.radius = s ∧ d.source = source ∧ d.totalSource = total ∧
        d.approximationError = error ∧ d.coordinates = u ∧ d.center = center ∧
        d.projectionNorm =
          ‖normalizeLocalL2 (hausdorff n X) (ball center ((1 / 2048) * s))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (affineResidual (hausdorff n X) hX.quadratic
              (radiusScaledColumns (hausdorff n X) hX.quadratic s u)
              (ball center ((1 / 2048) * s)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
              (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
                (ball center ((1 / 2048) * s))
                ((s ^ 2)⁻¹ • (T2.replacement i - T1.replacement i))))‖ := by
  classical
  obtain ⟨H, hH, haffine⟩ := projection_affine_bounds hgradient hmean hn hκ
  refine ⟨H, hH, ?_⟩
  intro root first center S1 S2 T1 T2 i s hroot hroom hcurv hsmallcurv hlap hvolume hsphere
    u V hfirst hnormal hcenter delta hdelta hmetric error herror hmeasured one hone cutoff
    hgrad1 hgrad2 source hsource hpair g coeff hrep hfit total htotal hsum hbudget
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hs : 0 < s := distanceSourceRadius_pos S2.radius_pos i
  have hsub : ball center (s / 512) ⊆ ball center (2 * s) := ball_subset_ball (by linarith)
  have hsub4 : ball center (s / 4) ⊆ ball center (2 * s) := ball_subset_ball (by linarith)
  have hconstant := ae_restrict_of_ae_restrict_of_subset hsub hone
  have hnormal' : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
      (ball center (2 * s)) measurableSet_ball (ContinuousLinearEquiv.refl ℝ (Euclidean n)) := by
    simpa only [IsExactMeanNormalization, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.comp_id] using hnormal
  have hid : transformedColumn μ hQ u (ContinuousLinearEquiv.refl ℝ (Euclidean n)) = u := by
    funext j
    simp only [transformedColumn, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.id_apply, sobolevColumnMap_single]
  have hfirst' : FirstOrderSplittingOn μ hQ center (2 * s) epsilon
      (transformedColumn μ hQ u (ContinuousLinearEquiv.refl ℝ (Euclidean n))) V := by
    rw [hid]
    exact hfirst
  have hrootradius : 2 * s ≤ root := distanceSourceRadius_outer_le S2.radius_pos.le i
  have haff (R : ℝ) (hRlo : s / 4096 ≤ R) (hRhi : R ≤ s)
      (hRcurv : -κ ≤ K * R ^ 2) (c : ℝ) (a : Euclidean n) :
      |c| + s * ‖a‖ ≤ H * ‖normalizeLocalL2 μ (ball center R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap μ hQ u (ball center R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖ := by
    simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl', id_eq] using
      haffine center s R hs hRlo hRhi hRcurv u V V
        (ContinuousLinearEquiv.refl ℝ (Euclidean n)) epsilon hepsilon hsmall
        hfirst.harmonic hfirst.continuous hcenter hfirst.representative hfirst' hnormal'
        (fun t ht hts => hvolume t ht (hts.trans hrootradius)) one
        (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hone) c a
  have hcurvR (R : ℝ) (hR : 0 ≤ R) (hRle : R ≤ s / 512) : -κ ≤ K * R ^ 2 := by
    by_cases hK : 0 ≤ K
    · exact (neg_nonpos.mpr hκ).trans (mul_nonneg hK (sq_nonneg R))
    · have hK' := le_of_not_ge hK
      have hsq : R ^ 2 ≤ (s / 512) ^ 2 := by nlinarith
      exact hsmallcurv.trans (mul_le_mul_of_nonpos_left hsq hK')
  have hcolumns := projection_coordinate_values μ hQ hs hdelta u V
    (ContinuousLinearEquiv.refl ℝ (Euclidean n)) hcenter
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hfirst.representative j))
    (by simpa only [ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using hmetric)
  have hradial (b : Euclidean n) : SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ g b) =ᵐ[
      μ.restrict (ball center (s / 512))] localGamma μ hQ (T2.replacement i) (sobolevColumnMap μ hQ u b) := by
    have hh := localRadialDerivative_column μ hQ (ball center (s / 512)) (T2.replacement i)
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith : s / 512 ≤ s / 4)) hgrad2)
      u g hrep b
    exact (SobolevSpace.restrictLp_coe μ hQ _ _).symm.trans
      (by rw [← hh]; exact localRadialDerivative_representative μ hQ _ _ _ _)
  have hlinear (b : Euclidean n) :
      sobolevColumnMap μ hQ (fun j => g j - sobolevColumnMap μ hQ u (coeff j)) b =
        sobolevColumnMap μ hQ g b - sobolevColumnMap μ hQ u (finiteCoefficientMap coeff b) := by
    have hh := centered_radial_residual_column μ hQ u g one 0 coeff b
    simpa only [centeredAffineSobolev, inner_zero_left, neg_zero, zero_smul, zero_add] using hh
  have hradialFit (b : Euclidean n) :
      ‖normalizeLocalL2 μ (ball center (s / 512)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball center (s / 512))
          (sobolevColumnMap μ hQ g b - sobolevColumnMap μ hQ u (finiteCoefficientMap coeff b)))‖ ≤
          ((n : ℝ) * Real.sqrt Drow) * s * ‖b‖ * source := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [← hlinear]
    have hh := normalized_column_sq_le μ hQ
      (fun j => g j - sobolevColumnMap μ hQ u (coeff j)) (ball center (s / 512))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (by positivity : 0 ≤ Drow * s ^ 2 * source ^ 2) hfit b
    convert hh using 1
    simp only [mul_pow, Real.sq_sqrt hDrow]
    ring
  let d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H
      ((n : ℝ) * Real.sqrt Drow) 1 1 := {
    root := root, root_le_one := hroot, first := first, center := center
    firstSource := S1, secondSource := S2, firstReplacement := T1, secondReplacement := T2
    index := i, room := hroom, curvature := hcurv, smallCurvature := hsmallcurv, laplacianBound := hlap
    coordinates := u, coordinateValues := fun x => s⁻¹ • V x
    harmonic := fun j => (hfirst.harmonic j).mono μ hQ hsub4
    gradient := fun j => ae_restrict_of_ae_restrict_of_subset hsub4 (hfirst.gradient j)
    firstGradient := hgrad1, secondGradient := hgrad2, cutoff := cutoff
    one := one, oneRepresentative := hconstant, volume := hvolume, sphere := hsphere
    frame := ContinuousLinearEquiv.refl ℝ (Euclidean n)
    frameBound := ContinuousLinearMap.norm_id_le
    source := source, source_pos := hsource, pairBudget := hpair
    affineBound := fun c a => haff (s / 2048) (by linarith) (by linarith)
      (hcurvR _ (by positivity) (by linarith)) c a
    affineHalfBound := fun c a => haff (s / 4096) le_rfl (by linarith)
      (hcurvR _ (by positivity) (by linarith)) c a
    columnBound := by simpa only [ContinuousLinearEquiv.coe_refl', id_eq, one_mul] using hcolumns
    radialColumns := sobolevColumnMap μ hQ g, radialMatrix := finiteCoefficientMap coeff
    radialRepresentative := hradial
    radialFit := by simpa only [ContinuousLinearEquiv.coe_refl', id_eq] using hradialFit
    totalSource := total, totalSource_nonneg := htotal, summable := hsum, totalBudget := hbudget
    approximationError := error, approximationError_pos := herror, measured := hmeasured
    centered := by rw [hcenter, smul_zero]
    representative := by
      intro j
      have hsub' : ball center ((1 / 1024) * s) ⊆ ball center (2 * s) := ball_subset_ball (by linarith)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub' (hfirst.representative j),
        ae_restrict_of_ae (Lp.coeFn_smul s⁻¹ (SobolevSpace.toLp μ hQ (u j)))] with x hx hsmul
      change SobolevSpace.toLp μ hQ (u j) x = V x j at hx
      change (s⁻¹ • SobolevSpace.toLp μ hQ (u j)) x = _
      simp only [hsmul, Pi.smul_apply, smul_eq_mul, hx, PiLp.smul_apply] }
  exact ⟨d, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RegularPointCoordinates

end

end OAI
