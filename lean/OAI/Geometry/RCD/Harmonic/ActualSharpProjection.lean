import OAI.Geometry.RCD.Harmonic.ActualProjectionConfiguration
import OAI.Geometry.RCD.Harmonic.ActualProjectionUnits
import OAI.Geometry.RCD.Sobolev.SharpProjectionGradient

namespace OAI

/-! # Sharp projection for the actual two-center Poisson targets -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Construct the compactness family from actual sources and replacements.
No residual, forcing, or outer estimate is assumed in the configuration. -/
theorem exists_actual_projection_family {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {κ B J C A Cχ epsilon H D L M : ℝ}
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∃ family : SharpProjectionFamily hX
      (ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) (1 / 1024) (1 / 2048),
      (∀ d, family.error d = d.error) ∧
      (∀ d, family.source d = d.source) ∧
      (∀ d, family.size d = d.projectionNorm) := by
  classical
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let I := ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M
  obtain ⟨F, G, T, hF, hG, hT, hchoose⟩ := actual_two_center_projection_outer hX
    hhessian hproduct hpoincare hgradient hn hκ hK hB hJ hCχ hA hepsilon hH hD hL
  have hdata (d : I) := hchoose d.first d.center d.firstSource d.secondSource
    d.firstReplacement d.secondReplacement d.index d.room d.coordinates d.harmonic d.gradient
    d.firstGradient d.secondGradient d.cutoff d.smallCurvature d.one d.oneRepresentative
    (fun t ht hts => d.volume t ht (hts.trans d.radius_le_root)) d.laplacianBound d.sphere
    d.frame d.source d.source_pos.le d.pairBudget d.affineBound d.affineHalfBound d.columnBound
    d.radialColumns d.radialMatrix d.radialRepresentative d.radialFit
  dsimp only at hdata
  choose c b k w e hweq hwharm hproj hcb heuler he hcoef houter using hdata
  let s : I → ℝ := fun d => d.radius
  let U : I → Fin n → SobolevSpace μ hQ := fun d => radiusScaledColumns μ hQ (s d) d.coordinates
  let f : I → SobolevSpace μ hQ := fun d => (s d ^ 2)⁻¹ • d.secondReplacement.replacement d.index
  let w' : I → SobolevSpace μ hQ := fun d => (s d ^ 2)⁻¹ • w d
  let e' : I → SobolevSpace μ hQ := fun d => (s d ^ 2)⁻¹ • e d
  let ell : I → Euclidean n := fun d => d.frame (b d) - d.radialMatrix (d.frame (b d))
  let alpha : I → ℝ := fun d => ‖normalizeLocalL2 μ (ball d.center ((1 / 2048) * s d))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp μ hQ (ball d.center ((1 / 2048) * s d)) (w' d))‖
  let A₀ := max (max 8 B) (max ((n : ℝ) + 1) (A ^ 2))
  let V₀ := Real.sqrt ((5 / 3 : ℝ) * (2 : ℝ) ^ n)
  have hA₀ : 0 ≤ A₀ := (by positivity : 0 ≤ max 8 B).trans (le_max_left _ _)
  have hAV : max 8 B ≤ A₀ := le_max_left _ _
  have hAn : (n : ℝ) + 1 ≤ A₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hAg : A ^ 2 ≤ A₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hs (d : I) : 0 < s d := d.radius_pos
  have hfrac1024 (d : I) : (1 / 1024 : ℝ) * s d = s d / 1024 := by ring
  have hfrac2048 (d : I) : (1 / 2048 : ℝ) * s d = s d / 2048 := by ring
  have hvol (d : I) (t : ℝ) (ht : 0 < t) (hts : t ≤ s d) :=
    d.volume t ht (hts.trans d.radius_le_root)
  have hgrad (d : I) : ∀ᵐ x ∂μ.restrict (ball d.center ((1 / 1024) * s d)),
      localGamma μ hQ (f d) (f d) x ≤ A₀ / s d ^ 2 := by
    have hh := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (show (1 / 1024 : ℝ) * s d ≤ s d / 4 by linarith [hs d])) d.secondGradient
    have hh' : ∀ᵐ x ∂μ.restrict (ball d.center ((1 / 1024) * s d)),
        localGamma μ hQ (d.secondReplacement.replacement d.index)
          (d.secondReplacement.replacement d.index) x ≤ A ^ 2 * s d ^ 2 := by
      simpa only [mul_pow, s, ActualProjectionConfiguration.radius, μ, hQ] using hh
    filter_upwards [rescaled_radial_energy μ hQ _ _ (hs d) hh'] with x hx
    apply (le_div_iff₀ (sq_pos_of_pos (hs d))).mpr
    simpa only [mul_comm] using hx.trans hAg
  have hp (d : I) : SobolevSpace.restrictLp μ hQ (ball d.center ((1 / 2048) * s d)) (w' d) =
      affineResidual μ hQ (U d) (ball d.center ((1 / 2048) * s d))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball d.center ((1 / 2048) * s d))
          ((s d ^ 2)⁻¹ • (d.secondReplacement.replacement d.index - d.firstReplacement.replacement d.index))) := by
    have hh := radius_scaled_projection μ hQ (hs d).ne' d.coordinates
      (ball d.center (s d / 2048)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (d.secondReplacement.replacement d.index - d.firstReplacement.replacement d.index)
      (w d) (hproj d)
    rw [hfrac2048 d]
    exact hh
  have hforce (d : I) : ‖normalizeLocalL2 μ (ball d.center ((1 / 1024) * s d))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ (ball d.center ((1 / 1024) * s d)) (e' d))‖ ≤
        (V₀ * F) * d.source := by
    have hsd := hs d
    have hposbig := (quarter_volume_bounds (by positivity : 0 < s d / 512)
      (euclideanUnitVolume_pos n) (hvol d (s d / 512) (by positivity) (by linarith [hs d]))).1
    have hpossmall := (quarter_volume_bounds (by positivity : 0 < s d / 1024)
      (euclideanUnitVolume_pos n) (hvol d (s d / 1024) (by positivity) (by linarith [hs d]))).1
    have hv := radial_fraction_volume_ratio (by positivity : 0 < s d / 512)
      (by norm_num : (0 : ℝ) < 1 / 2) (euclideanUnitVolume_pos n)
      (hvol d (s d / 512) (by positivity) (by linarith [hs d]))
      (hvol d ((1 / 2) * (s d / 512)) (by positivity) (by linarith [hs d]))
    have hrad : (1 / 2 : ℝ) * (s d / 512) = s d / 1024 := by ring
    have hpow : ((1 / 2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ n := by simp
    rw [hrad, hpow] at hv
    have hv' : μ.real (ball d.center (s d / 512)) ≤ V₀ ^ 2 * μ.real (ball d.center (s d / 1024)) := by
      dsimp only [V₀]
      rw [Real.sq_sqrt (by positivity)]
      exact (div_le_iff₀ hpossmall).mp hv
    have he' : ‖normalizeLocalL2 μ (ball d.center (s d / 512))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball d.center (s d / 512)) (e' d))‖ ≤ F * d.source := by
      dsimp only [e']
      rw [map_smul, normalizeLocalL2_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (sq_pos_of_pos (hs d)))]
      calc
        _ ≤ (s d ^ 2)⁻¹ * (F * s d ^ 2 * d.source) :=
          mul_le_mul_of_nonneg_left (he d) (by positivity)
        _ = F * d.source := by field_simp [hsd.ne']
    have hb := normalized_fit_restrict_norm μ hQ
      (ball_subset_ball (show s d / 1024 ≤ s d / 512 by linarith [hs d]))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hposbig hpossmall (e' d)
      (Real.sqrt_nonneg _) (mul_nonneg hF d.source_pos.le) hv' he'
    rw [normalized_sobolev_norm_congr μ hQ (congrArg (ball d.center) (hfrac1024 d))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (e' d)]
    exact hb.trans_eq (by ring)
  have hcoef' (d : I) : ‖(s d)⁻¹ • ell d‖ + |(s d ^ 2)⁻¹ * k d| ≤
      (max 1 (2048 * M) * G) * (alpha d + d.source) := by
    have hb := projection_coefficient_rescale d.frame (hs d) d.frameBound (ell d) (k d) (hcoef d)
    dsimp only [alpha]
    rw [normalized_sobolev_norm_congr μ hQ (congrArg (ball d.center) (hfrac2048 d))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (w' d)]
    exact hb
  let family : SharpProjectionFamily hX I (1 / 1024) (1 / 2048) := {
    center := fun d => d.center
    radius := s
    error := fun d => d.error
    source := fun d => d.source
    coordinates := U
    coordinateValues := fun d => d.coordinateValues
    radial := f
    target := fun d => (s d ^ 2)⁻¹ • (d.secondReplacement.replacement d.index - d.firstReplacement.replacement d.index)
    residual := w'
    forcing := e'
    coefficient := fun d => (s d)⁻¹ • ell d
    constant := fun d => (s d ^ 2)⁻¹ * k d
    size := alpha
    radialBound := A₀
    outerConstant := T
    coefficientConstant := max 1 (2048 * M) * G
    sourceConstant := V₀ * F
    radius_pos := hs
    curvature := fun d => d.curvature
    error_pos := fun d => d.error_pos hB
    source_pos := fun d => d.source_pos
    radialBound_nonneg := hA₀
    outerConstant_nonneg := hT
    coefficientConstant_nonneg := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hG
    measured := fun d => d.measured.mono_error (d.approximationError_le hB)
    representative := fun d => d.representative
    laplacianCoefficient := fun d => (n : ℝ) + κ * (4 * s d) ^ 2
    laplacianCoefficient_bound := by
      intro d
      rw [abs_of_nonneg (by positivity)]
      exact d.laplacianBound.trans hAn
    laplacian := by
      intro d
      apply rescaled_radial_laplacian μ hQ
      exact (d.secondReplacement.laplacian d.index).mono μ hQ measurableSet_ball
        (ball_subset_ball (show (1 / 1024 : ℝ) * s d ≤ s d by linarith [hs d]))
    radial_norm := by
      intro d
      apply normalized_norm_le_of_bound μ _ _ _ hA₀
      have hvalue := rescaled_radial_value μ hQ (ball d.center ((1 / 1024) * s d))
        (d.secondReplacement.replacement d.index) (hs d)
        (ae_restrict_of_ae (d.secondReplacement.value_bound μ hQ d.index))
      filter_upwards [hvalue, SobolevSpace.restrictLp_coe μ hQ _ (f d)] with x hx heq
      rw [heq]
      exact hx.trans hAV
    gradient := hgrad
    quadratic_error := fun d => d.quadratic_error hn hκ hB
    harmonic := by
      intro d
      exact ((hwharm d).mono μ hQ (ball_subset_ball
        (show (1 / 1024 : ℝ) * s d ≤ s d / 512 by linarith [hs d]))).smul μ hQ _
    projection := hp
    size_eq := fun _ => rfl
    outer_bound := by
      intro d
      dsimp only [alpha]
      rw [normalized_sobolev_norm_congr μ hQ (congrArg (ball d.center) (hfrac1024 d))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (w' d),
        normalized_sobolev_norm_congr μ hQ (congrArg (ball d.center) (hfrac2048 d))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (w' d)]
      exact houter d
    coefficient_bound := hcoef'
    forcing_bound := hforce
    euler_identity := by
      intro d
      have hsub : ball d.center ((1 / 1024) * s d) ⊆ ball d.center (s d / 512) :=
        ball_subset_ball (by linarith [hs d])
      have heta := ae_restrict_of_ae_restrict_of_subset hsub d.oneRepresentative
      have hf := ae_restrict_of_ae_restrict_of_subset
        (ball_subset_ball (show (1 / 1024 : ℝ) * s d ≤ s d / 4 by linarith [hs d])) d.secondGradient
      have hid : localRadialDerivative μ hQ (ball d.center ((1 / 1024) * s d))
          (d.secondReplacement.replacement d.index) hf (w d) =
          SobolevSpace.restrictLp μ hQ (ball d.center ((1 / 1024) * s d))
            (w d + sobolevColumnMap μ hQ d.coordinates (ell d) + k d • d.one + e d) :=
        localRadialDerivative_eq_restrict μ hQ _ _ _ _ hf
          (ae_restrict_of_ae_restrict_of_subset hsub (heuler d).symm)
      exact radius_scaled_projection_euler_sum μ hQ (hs d) _ _ d.coordinates
        (d.secondReplacement.replacement d.index) (w d) d.one (e d) (ell d) (k d) heta hf (hgrad d) hid
  }
  refine ⟨family, fun _ => rfl, fun _ => rfl, ?_⟩
  intro d
  change alpha d = d.projectionNorm
  dsimp only [alpha, ActualProjectionConfiguration.projectionNorm]
  rw [hp d]

/-- One sharp estimate for every actual two-center target satisfying the
preceding geometric estimates. The only compactness input is the precise
published Poisson/harmonic convergence theorem. -/
theorem actual_sharp_projection {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hcompact : LocalPoissonHarmonicCompactnessInput hX) (hn : 2 ≤ n)
    {κ B J C A Cχ epsilon H D L M : ℝ}
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∃ P : ℝ, 0 < P ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M,
        d.error < delta → d.projectionNorm ≤ P * d.source := by
  obtain ⟨family, herr, hsource, hnorm⟩ := exists_actual_projection_family hX
    hhessian hproduct hpoincare hgradient hn hκ hK hB hJ hCχ hA hepsilon hH hD hL
  obtain ⟨P, hP, delta, hdelta, hbound⟩ := family.uniform_bound hcompact hgradient hn
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨P, hP, delta, hdelta, ?_⟩
  intro d hd
  simpa only [hsource d, hnorm d] using hbound d (by simpa only [herr d] using hd)

/-- The same sharp estimate controls the actual harmonic residual gradient
on the smaller testing ball, in physical radius units. -/
theorem actual_sharp_projection_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hcompact : LocalPoissonHarmonicCompactnessInput hX) (hn : 2 ≤ n)
    {κ B J C A Cχ epsilon H D L M : ℝ}
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∃ Q : ℝ, 0 < Q ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M,
        d.error < delta → ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball d.center ((1 / 2048) * d.radius)) w →
      SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball d.center ((1 / 2048) * d.radius)) w =
        affineResidual (hausdorff n X) hX.quadratic
          (radiusScaledColumns (hausdorff n X) hX.quadratic d.radius d.coordinates)
          (ball d.center ((1 / 2048) * d.radius))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
            (ball d.center ((1 / 2048) * d.radius))
            ((d.radius ^ 2)⁻¹ • (d.secondReplacement.replacement d.index - d.firstReplacement.replacement d.index))) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball d.center ((1 / 4096) * d.radius)),
        d.radius ^ 2 * localGamma (hausdorff n X) hX.quadratic w w x ≤ Q ^ 2 * d.source ^ 2 := by
  obtain ⟨P, hP, delta, hdelta, hbound⟩ := actual_sharp_projection (C := C) (M := M) hX
    hhessian hproduct hpoincare hgradient hcompact hn hκ hK hB hJ hCχ hA hepsilon hH hD hL
  obtain ⟨Cg, hCg, hgrad⟩ := hgradient hn ((1 / 2048 : ℝ) ^ 2) (1 / 2)
    (sq_nonneg _) (by norm_num) (by norm_num)
  refine ⟨2048 * Cg * P, mul_pos (mul_pos (by norm_num) (by linarith)) hP, delta, hdelta, ?_⟩
  intro d hd w hwharm hw
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hr := d.radius_pos
  have hcurv : -((1 / 2048 : ℝ) ^ 2) ≤ K * ((1 / 2048) * d.radius) ^ 2 := by
    have hc := d.curvature
    change -1 ≤ K * d.radius ^ 2 at hc
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg (1 / 2048 : ℝ))
    nlinarith only [hh]
  have hnrm : ‖normalizeLocalL2 μ (ball d.center ((1 / 2048) * d.radius))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ (ball d.center ((1 / 2048) * d.radius)) w)‖ = d.projectionNorm := by
    rw [hw]
    rfl
  have hmean : (μ.real (ball d.center ((1 / 2048) * d.radius)))⁻¹ *
      (∫ x in ball d.center ((1 / 2048) * d.radius), (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) =
        d.projectionNorm ^ 2 := by
    rw [← normalized_sobolev_mean_sq μ hQ _ (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)), hnrm]
  have hg := hgrad d.center ((1 / 2048) * d.radius) (by positivity) hcurv w hwharm
  change ∀ᵐ x ∂μ.restrict (ball d.center ((1 / 2) * ((1 / 2048) * d.radius))),
    localGamma μ hQ w w x ≤ _ at hg
  rw [hmean] at hg
  have hsize : d.projectionNorm ^ 2 ≤ (P * d.source) ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_pos hP d.source_pos).le).mpr
    exact hbound d hd
  have hrad : (1 / 2 : ℝ) * ((1 / 2048) * d.radius) = (1 / 4096) * d.radius := by ring
  rw [hrad] at hg
  filter_upwards [hg] with x hx
  calc
    _ ≤ d.radius ^ 2 * ((Cg / ((1 / 2048) * d.radius)) ^ 2 * d.projectionNorm ^ 2) :=
      mul_le_mul_of_nonneg_left hx (sq_nonneg _)
    _ ≤ d.radius ^ 2 * ((Cg / ((1 / 2048) * d.radius)) ^ 2 * (P * d.source) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsize (sq_nonneg _)) (sq_nonneg _)
    _ = (2048 * Cg * P) ^ 2 * d.source ^ 2 := by field_simp [hr.ne']

end RegularPointCoordinates

end

end OAI
