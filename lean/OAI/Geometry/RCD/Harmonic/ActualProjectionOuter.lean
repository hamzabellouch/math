import OAI.Geometry.RCD.Harmonic.ActualTwoCenterProjection
import OAI.Geometry.RCD.Coordinates.NormalizedTransportDefect
import OAI.Geometry.RCD.Harmonic.ScaledProjectionOuter
import OAI.Geometry.RCD.Harmonic.ProjectionResidualValues

namespace OAI

/-! # Uniform outer estimates for the actual two-center Poisson projection -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The same actual projection satisfies a uniform outer estimate. The
transport error is constructed from the second Poisson replacement and its
full source measure. All three constants precede the centers and scales. -/
theorem actual_two_center_projection_outer {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {κ B J C A Cχ epsilon H D L : ℝ}
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∃ F G₀ T₀ : ℝ, 0 ≤ F ∧ 0 ≤ G₀ ∧ 0 ≤ T₀ ∧ ∀ {r0 : ℝ} (p₁ p₂ : X)
    (S₁ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₁ r0)
    (S₂ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₂ r0)
    (T₁ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₁ B J C)
    (T₂ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₂ B J C)
    (i : ℕ)
    (_hroom₁ : dist p₂ p₁ ≤ distanceSourceRadius r0 i / 4)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (_hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball p₂ (distanceSourceRadius r0 i / 4)) (u j))
    (_hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p₂ (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (_hf₁ : ∀ᵐ x ∂(hausdorff n X).restrict (ball p₂ (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₁.replacement i) (T₁.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (_hf₂ : ∀ᵐ x ∂(hausdorff n X).restrict (ball p₂ (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i) (T₂.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (_χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p₂ (distanceSourceRadius r0 i / 64) Cχ)
    (_hcurv : -κ ≤ K * (distanceSourceRadius r0 i / 512) ^ 2)
    (η : SobolevSpace (hausdorff n X) hX.quadratic)
    (_hη : SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
      (hausdorff n X).restrict (ball p₂ (distanceSourceRadius r0 i / 512))]
      fun _ => (1 : ℝ))
    (_hvolume : ∀ t : ℝ, 0 < t → t ≤ distanceSourceRadius r0 i →
      |(hausdorff n X).real (ball p₂ t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4)
    (_ha : (n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2 ≤ (n : ℝ) + 1)
    (_hsphere : (hausdorff n X) (sphere p₂ (distanceSourceRadius r0 i / 2048)) = 0)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (σ : ℝ) (_hσ : 0 ≤ σ)
    (_hbudget : normalizedPoissonDefect (hausdorff n X) hX.quadratic S₁ i +
      normalizedPoissonDefect (hausdorff n X) hX.quadratic S₂ i ≤ σ ^ 2)
    (_hbound : ∀ c a, |c| + distanceSourceRadius r0 i * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 (hausdorff n X) (ball p₂ (distanceSourceRadius r0 i / 2048))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap (hausdorff n X) hX.quadratic u
          (ball p₂ (distanceSourceRadius r0 i / 2048))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖)
    (_hboundHalf : ∀ c a, |c| + distanceSourceRadius r0 i * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 (hausdorff n X) (ball p₂ (distanceSourceRadius r0 i / 4096))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap (hausdorff n X) hX.quadratic u
          (ball p₂ (distanceSourceRadius r0 i / 4096))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖)
    (_hcolumn : ∀ b : Euclidean n, ∀ᵐ x ∂(hausdorff n X).restrict
      (ball p₂ (distanceSourceRadius r0 i / 512)),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u (N b)) x| ≤
          L * distanceSourceRadius r0 i * ‖b‖)
    (G : Euclidean n →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (Az : Euclidean n →L[ℝ] Euclidean n)
    (_hG : ∀ b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (G b) =ᵐ[
      (hausdorff n X).restrict (ball p₂ (distanceSourceRadius r0 i / 512))]
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u b))
    (_hfit : ∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball p₂ (distanceSourceRadius r0 i / 512))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball p₂ (distanceSourceRadius r0 i / 512))
        (G (N b) - sobolevColumnMap (hausdorff n X) hX.quadratic u (Az (N b))))‖ ≤
          D * distanceSourceRadius r0 i * ‖b‖ * σ),
    ∃ (c : ℝ) (b : Euclidean n) (k : ℝ)
      (w e : SobolevSpace (hausdorff n X) hX.quadratic),
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let Ω := ball p₂ (s / 512)
      let I := ball p₂ (s / 2048)
      w = T₂.replacement i - T₁.replacement i - c • η - sobolevColumnMap μ hX.quadratic u (N b) ∧
      IsSobolevHarmonicOn μ hX.quadratic Ω w ∧
      SobolevSpace.restrictLp μ hX.quadratic I w = affineResidual μ hX.quadratic u I
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic I (T₂.replacement i - T₁.replacement i)) ∧
      |c| + s * ‖b‖ ≤ H * (2 * max 8 B) * s ^ 2 ∧
      (localGamma μ hX.quadratic (T₂.replacement i) w =ᵐ[μ.restrict Ω]
        SobolevSpace.toLp μ hX.quadratic
          (w + sobolevColumnMap μ hX.quadratic u (N b - Az (N b)) + k • η + e)) ∧
      ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic Ω e)‖ ≤ F * s ^ 2 * σ ∧
      |(s ^ 2)⁻¹ * k| + (s / 2048) * ‖N.symm ((s ^ 2)⁻¹ • (N b - Az (N b)))‖ ≤
        G₀ * (‖normalizeLocalL2 μ I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp μ hX.quadratic I ((s ^ 2)⁻¹ • w))‖ + σ) ∧
      ‖normalizeLocalL2 μ (ball p₂ (s / 1024))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic (ball p₂ (s / 1024)) ((s ^ 2)⁻¹ • w))‖ ≤
        T₀ * (‖normalizeLocalL2 μ I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp μ hX.quadratic I ((s ^ 2)⁻¹ • w))‖ + σ) := by
  obtain ⟨F, hF, hprojection⟩ := actual_two_center_projection hX hhessian hproduct hpoincare
    hκ hK hB hJ hCχ hA hepsilon hH hD
  let V₀ := Real.sqrt ((5 / 3 : ℝ) * (2 : ℝ) ^ n)
  let W₀ := Real.sqrt ((5 / 3 : ℝ) * (4 : ℝ) ^ n)
  let D₀ := Real.sqrt (B * (2048 : ℝ) ^ 2 *
    ((4 / (3 * euclideanUnitVolume n)) * (2048 : ℝ) ^ n))
  let Cw : ℝ≥0 := ⟨2 * max 8 B + (1 + L) * H * (2 * max 8 B), by positivity⟩
  obtain ⟨G₀, T₀, hG₀, hT₀, houter⟩ := hgradient.scaled_projected_residual_outer hn hκ hH
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2048) hA)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2048) hL) hF Cw (D := D₀)
  refine ⟨F, G₀, T₀, hF, hG₀, hT₀, ?_⟩
  intro r0 p₁ p₂ S₁ S₂ T₁ T₂ i hroom₁ u hu hgrad hf₁ hf₂ χ hcurv η hη hvolume ha hsphere
    N σ hσ hbudget hbound hboundHalf hcolumn G Az hG hfit
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  let R := s / 2048
  let Ω := ball p₂ (s / 512)
  let I := ball p₂ R
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  have hR : 0 < R := by dsimp only [R]; positivity
  have hv (t : ℝ) (ht : 0 < t) (hts : t ≤ s) := hvolume t ht hts
  obtain ⟨c, b, k, w, e, hweq, hwharm, hproj, hcoeff, heuler, he⟩ :=
    hprojection p₁ p₂ p₂ S₁ S₂ T₁ T₂ i hroom₁
      (by rw [dist_self]; change 0 ≤ s / 4; positivity) u hu hgrad hf₁ hf₂ χ hcurv η hη
      (hv (s / 64) (by positivity) (by linarith))
      (hv (s / 512) (by positivity) (by linarith)) N σ hσ hbudget hbound G Az hG hfit
  have hpositive : 0 < μ.real I :=
    (quarter_volume_bounds hR (euclideanUnitVolume_pos n)
      (hv R hR (by dsimp only [R]; linarith))).1
  have hhalfpos : 0 < μ.real (ball p₂ (R / 2)) :=
    (quarter_volume_bounds (by positivity : 0 < R / 2) (euclideanUnitVolume_pos n)
      (hv (R / 2) (by positivity) (by dsimp only [R]; linarith))).1
  have hhalf : μ.real (ball p₂ R) ≤ V₀ ^ 2 * μ.real (ball p₂ (R / 2)) := by
    have hh := radial_fraction_volume_ratio hR (by norm_num : (0:ℝ) < 1 / 2)
      (euclideanUnitVolume_pos n) (hv R hR (by dsimp only [R]; linarith))
      (hv ((1 / 2) * R) (by positivity) (by dsimp only [R]; linarith))
    have hpow : ((1 / 2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ n := by simp
    rw [one_div_mul_eq_div, hpow] at hh
    dsimp only [V₀]
    rw [Real.sq_sqrt (by positivity)]
    exact (div_le_iff₀ hhalfpos).mp hh
  have hfour : μ.real (ball p₂ (4 * R)) ≤ W₀ ^ 2 * μ.real I := by
    have hh := radial_fraction_volume_ratio (by positivity : 0 < 4 * R)
      (by norm_num : (0:ℝ) < 1 / 4) (euclideanUnitVolume_pos n)
      (hv (4 * R) (by positivity) (by dsimp only [R]; linarith))
      (hv ((1 / 4) * (4 * R)) (by positivity) (by dsimp only [R]; linarith))
    have hpow : ((1 / 4 : ℝ) ^ n)⁻¹ = (4 : ℝ) ^ n := by simp
    have heq : (1 / 4 : ℝ) * (4 * R) = R := by ring
    rw [heq, hpow] at hh
    dsimp only [W₀]
    rw [Real.sq_sqrt (by positivity)]
    exact (div_le_iff₀ hpositive).mp hh
  have hwvalue : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ w x| ≤ Cw * s ^ 2 := by
    have hvv : ∀ᵐ x ∂μ.restrict Ω,
        |SobolevSpace.toLp μ hQ (T₂.replacement i - T₁.replacement i) x| ≤ (2 * max 8 B) * s ^ 2 := by
      filter_upwards [ae_restrict_of_ae (T₁.value_bound μ hQ i),
        ae_restrict_of_ae (T₂.value_bound μ hQ i),
        ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ (T₂.replacement i))
          (SobolevSpace.toLp μ hQ (T₁.replacement i)))] with x h1 h2 hsub
      rw [map_sub, hsub, Pi.sub_apply]
      exact (abs_sub _ _).trans (by dsimp only [s] at *; linarith)
    have hb := physical_projection_residual_bound μ hQ Ω u N
      (T₂.replacement i - T₁.replacement i) η c b hs hH (by positivity) hL hvv hη (hcolumn b) hcoeff
    have hscale : s ^ 2 • ((s ^ 2)⁻¹ • w) = w := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hs)), one_smul]
    rw [← hweq] at hb
    filter_upwards [hb, ae_restrict_of_ae (Lp.coeFn_smul (s ^ 2)
      (SobolevSpace.toLp μ hQ ((s ^ 2)⁻¹ • w)))] with x hb heq
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
    rw [← hscale, map_smul, heq, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (sq_nonneg s)]
    exact hh.trans_eq (mul_comm _ _)
  have hbound' : ∀ c a, |c| + R * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 μ (ball p₂ (R / 2))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap μ hQ u (ball p₂ (R / 2))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖ := by
    intro c a
    have hh := hboundHalf c a
    have heq : R / 2 = s / 4096 := by dsimp only [R]; ring
    rw [heq]
    exact (by dsimp only [R]; nlinarith [norm_nonneg (N.symm a)] :
      |c| + R * ‖N.symm a‖ ≤ |c| + s * ‖N.symm a‖).trans hh
  have hU (v : Euclidean n) : ‖normalizeLocalL2 μ Ω
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ u v))‖ ≤ (2048 * L) * (R * ‖N.symm v‖) := by
    have hh := normalized_norm_le_of_bound μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ u v))
      (by positivity : 0 ≤ L * s * ‖N.symm v‖) ?_
    · convert hh using 1; dsimp only [R]; ring
    filter_upwards [hcolumn (N.symm v), SobolevSpace.restrictLp_coe μ hQ Ω
      (sobolevColumnMap μ hQ u v)] with x hx heq
    rw [heq]
    simpa only [N.apply_symm_apply] using hx
  have hf : ∀ᵐ x ∂μ.restrict (ball p₂ (4 * R)),
      localGamma μ hQ (T₂.replacement i) (T₂.replacement i) x ≤ ((2048 * A) * R) ^ 2 := by
    have hh := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (show 4 * R ≤ s / 4 by dsimp only [R]; linarith)) hf₂
    have heq : ((2048 * A) * R) ^ 2 = (A * s) ^ 2 := by dsimp only [R]; ring
    rw [heq]
    exact hh
  have hlap := (T₂.laplacian i).mono μ hQ measurableSet_ball
    (ball_subset_ball (show 4 * R ≤ s by dsimp only [R]; linarith))
  have hid : localRadialDerivative μ hQ (ball p₂ (4 * R)) (T₂.replacement i) hf w =
      SobolevSpace.restrictLp μ hQ (ball p₂ (4 * R))
        (w + sobolevColumnMap μ hQ u (N b - Az (N b)) + k • η + e) := by
    apply localRadialDerivative_eq_restrict
    have h4 : 4 * R = s / 512 := by dsimp only [R]; ring
    simpa only [h4] using heuler.symm
  have hbudget₂ : normalizedPoissonDefect μ hQ S₂ i ≤ σ ^ 2 := by
    have hp := normalizedPoissonDefect_nonneg μ hQ S₁ hκ i
    linarith
  obtain ⟨g, hg, hradial, hgerror⟩ := T₂.normalized_transport_defect μ hQ i hκ hB hbudget₂
    (hv R hR (by dsimp only [R]; linarith))
  have hgerror' : (∫ x in ball p₂ (4 * R), (g x) ^ 2 ∂μ) ≤
      D₀ ^ 2 * R ^ 2 * μ.real I * σ ^ 2 := by
    have homega := euclideanUnitVolume_pos n
    dsimp only [D₀]
    rw [Real.sq_sqrt (by positivity)]
    exact hgerror
  have hcurvR : -κ ≤ K * R ^ 2 := by
    have hh : K * R ^ 2 = (K * (s / 512) ^ 2) / 16 := by dsimp only [R]; ring
    rw [hh]
    linarith
  have hsmall : IsSobolevHarmonicOn μ hQ (ball p₂ R) w :=
    hwharm.mono μ hQ (ball_subset_ball (show R ≤ s / 512 by dsimp only [R]; linarith))
  have h4 : 4 * R = s / 512 := by dsimp only [R]; ring
  have h2 : 2 * R = s / 1024 := by dsimp only [R]; ring
  have hb := houter p₂ R ((n : ℝ) + κ * (4 * s) ^ 2) s hR (by positivity) ha hcurvR hs
    (T₂.replacement i) w η e u N (N b - Az (N b)) k σ hσ hlap hf
    (by simpa only [h4] using hwvalue) hsmall
    (by simpa only [h4] using hη) hpositive hhalf hfour hbound' hid
    (by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr he
      rw [normalized_sobolev_mean_sq] at hh ⊢
      simpa only [h4] using hh) (fun v => by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hU v)
      rw [normalized_sobolev_mean_sq] at hh ⊢
      simpa only [h4] using hh)
    g hg hradial hsphere hgerror'
  refine ⟨c, b, k, w, e, hweq, hwharm, hproj, hcoeff, heuler, he, hb.1, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb.2
  rw [normalized_sobolev_mean_sq] at hh ⊢
  simpa only [h2] using hh

end RegularPointCoordinates

end

end OAI
