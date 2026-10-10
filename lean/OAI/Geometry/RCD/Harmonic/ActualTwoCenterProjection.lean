import OAI.Geometry.RCD.Sobolev.ActualPoissonEulerForcing
import OAI.Geometry.RCD.Sobolev.PhysicalProjectionEuler

namespace OAI

/-! # The actual two-center Poisson projection and its scalar forcing -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The projected function is constructed from the two actual Poisson
replacements. Its scalar forcing is controlled by the original defects
and the already constructed coordinate radial fits. The constant precedes
all centers, root radii and dyadic indices. -/
theorem actual_two_center_projection {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    {κ B J C A Cχ epsilon H D : ℝ}
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hH : 0 ≤ H) (hD : 0 ≤ D) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {r0 : ℝ} (p₁ p₂ z : X)
    (S₁ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₁ r0)
    (S₂ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₂ r0)
    (T₁ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₁ B J C)
    (T₂ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₂ B J C)
    (i : ℕ)
    (_hroom₁ : dist z p₁ ≤ distanceSourceRadius r0 i / 4)
    (_hroom₂ : dist z p₂ ≤ distanceSourceRadius r0 i / 4)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (_hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball z (distanceSourceRadius r0 i / 4)) (u j))
    (_hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (_hf₁ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₁.replacement i) (T₁.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (_hf₂ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i) (T₂.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (_χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic z (distanceSourceRadius r0 i / 64) Cχ)
    (_hcurv : -κ ≤ K * (distanceSourceRadius r0 i / 512) ^ 2)
    (η : SobolevSpace (hausdorff n X) hX.quadratic)
    (_hη : SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
      (hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 512))]
      fun _ => (1 : ℝ))
    (_hvolume : |(hausdorff n X).real (ball z (distanceSourceRadius r0 i / 64)) /
      (euclideanUnitVolume n * (distanceSourceRadius r0 i / 64) ^ n) - 1| ≤ 1 / 4)
    (_hvolumeSmall : |(hausdorff n X).real (ball z (distanceSourceRadius r0 i / 512)) /
      (euclideanUnitVolume n * (distanceSourceRadius r0 i / 512) ^ n) - 1| ≤ 1 / 4)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (σ : ℝ) (_hσ : 0 ≤ σ)
    (_hbudget : normalizedPoissonDefect (hausdorff n X) hX.quadratic S₁ i +
      normalizedPoissonDefect (hausdorff n X) hX.quadratic S₂ i ≤ σ ^ 2)
    (_hbound : ∀ c a, |c| + distanceSourceRadius r0 i * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 (hausdorff n X) (ball z (distanceSourceRadius r0 i / 2048))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineCoordinateMap (hausdorff n X) hX.quadratic u
          (ball z (distanceSourceRadius r0 i / 2048))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖)
    (G : Euclidean n →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (Az : Euclidean n →L[ℝ] Euclidean n)
    (_hG : ∀ b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (G b) =ᵐ[
      (hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 512))]
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u b))
    (_hfit : ∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball z (distanceSourceRadius r0 i / 512))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball z (distanceSourceRadius r0 i / 512))
        (G (N b) - sobolevColumnMap (hausdorff n X) hX.quadratic u (Az (N b))))‖ ≤
          D * distanceSourceRadius r0 i * ‖b‖ * σ),
    ∃ (c : ℝ) (b : Euclidean n) (k : ℝ)
      (w e : SobolevSpace (hausdorff n X) hX.quadratic),
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let Ω := ball z (s / 512)
      let I := ball z (s / 2048)
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
        (SobolevSpace.restrictLp μ hX.quadratic Ω e)‖ ≤ F * s ^ 2 * σ := by
  obtain ⟨Cp, hCp, hforcing⟩ := actual_poisson_euler_forcing hX hhessian hproduct hpoincare hκ
  let E := Real.sqrt ((Cp / 512) ^ 2 * ((5 / 3 : ℝ) * (8 : ℝ) ^ n) *
    poissonEulerGradientConstant n A B J Cχ)
  let V := 2 * max 8 B
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  refine ⟨E + D * H * V, by dsimp only [E]; positivity, ?_⟩
  intro r0 p₁ p₂ z S₁ S₂ T₁ T₂ i hroom₁ hroom₂ u hu hgrad hf₁ hf₂ χ
    hcurv η hη hvolume hvolumeSmall N σ hσ hbudget hbound G Az hG hfit
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  let Ω := ball z (s / 512)
  let I := ball z (s / 2048)
  let v := T₂.replacement i - T₁.replacement i
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  have hsub : I ⊆ Ω := ball_subset_ball (by dsimp only [s]; linarith)
  have hbig : Ω ⊆ ball z (s / 4) := ball_subset_ball (by linarith)
  have hhu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j) :=
    fun j => (hu j).mono μ hQ hbig
  have hv : IsSobolevHarmonicOn μ hQ Ω v :=
    common_replacement_difference_harmonic μ hQ T₁ T₂ i z
      (by change s / 512 + dist z p₁ ≤ s; change dist z p₁ ≤ s / 4 at hroom₁; linarith)
      (by change s / 512 + dist z p₂ ≤ s; change dist z p₂ ≤ s / 4 at hroom₂; linarith)
  have hfv : ∀ T : DyadicDistanceReplacements μ hQ S₁ B J C,
      ‖normalizeLocalL2 μ I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ I (T.replacement i))‖ ≤ max 8 B * s ^ 2 := by
    intro T
    apply normalized_norm_le_of_bound μ I _ _ (by have : 0 ≤ max 8 B := le_trans (by norm_num) (le_max_left _ _); positivity)
    filter_upwards [ae_restrict_of_ae (T.value_bound μ hQ i),
      SobolevSpace.restrictLp_coe μ hQ I (T.replacement i)] with x hx heq
    rw [heq]
    exact hx
  have hfv₂ : ‖normalizeLocalL2 μ I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ I (T₂.replacement i))‖ ≤ max 8 B * s ^ 2 := by
    apply normalized_norm_le_of_bound μ I _ _ (by have : 0 ≤ max 8 B := le_trans (by norm_num) (le_max_left _ _); positivity)
    filter_upwards [ae_restrict_of_ae (T₂.value_bound μ hQ i),
      SobolevSpace.restrictLp_coe μ hQ I (T₂.replacement i)] with x hx heq
    rw [heq]
    exact hx
  have hvalue : ‖normalizeLocalL2 μ I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ I v)‖ ≤ V * s ^ 2 := by
    have hh := (norm_sub_le
      (normalizeLocalL2 μ I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ I (T₂.replacement i)))
      (normalizeLocalL2 μ I (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ I (T₁.replacement i)))).trans (add_le_add hfv₂ (hfv T₁))
    simpa only [v, map_sub, normalizeLocalL2, smul_sub, V, two_mul, add_mul] using hh
  obtain ⟨k, ev, hevId, hev⟩ := hforcing hK hB hJ hCχ hA hepsilon p₁ p₂ z S₁ S₂ T₁ T₂ i
    hroom₁ hroom₂ u hu hgrad hf₁ hf₂ χ hcurv η hη hvolume hvolumeSmall
  have hE2 : E ^ 2 = (Cp / 512) ^ 2 * ((5 / 3 : ℝ) * (8 : ℝ) ^ n) *
      poissonEulerGradientConstant n A B J Cχ := by
    apply Real.sq_sqrt
    have homega := euclideanUnitVolume_pos n
    dsimp only [poissonEulerGradientConstant]
    positivity
  have heScale : ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ Ω ((s ^ 2)⁻¹ • ev))‖ ≤ E * σ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by dsimp only [E]; positivity)).mp
    rw [mul_pow, hE2]
    exact hev.trans (mul_le_mul_of_nonneg_left hbudget (by rw [← hE2]; positivity))
  have hev' : ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hQ Ω ev)‖ ≤ E * s ^ 2 * σ := by
    rw [map_smul, normalizeLocalL2_smul, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (sq_pos_of_pos hs)] at heScale
    have hh := mul_le_mul_of_nonneg_left heScale (sq_nonneg s)
    field_simp [hs.ne'] at hh
    nlinarith only [hh]
  have hf := ae_restrict_of_ae_restrict_of_subset hbig hf₂
  have hvId := localRadialDerivative_eq_of_euler μ hQ Ω (T₂.replacement i) v η ev hf k hη hevId
  have hGId (a) := localRadialDerivative_eq_restrict μ hQ Ω (T₂.replacement i)
    (sobolevColumnMap μ hQ u a) (G a) hf (hG a)
  obtain ⟨c, b, hw, hproj, hcoef, hid, he⟩ := physical_projection_euler μ hQ u I Ω
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hsub measurableSet_ball hhu
    (T₂.replacement i) v η ev hv hη N hs hH hV (Real.sqrt_nonneg _) hD hσ
    hbound hvalue hf G Az k hvId hGId hev' hfit
  let w := v - c • η - sobolevColumnMap μ hQ u (N b)
  let e := ev - (G (N b) - sobolevColumnMap μ hQ u (Az (N b)))
  refine ⟨c, b, k + c, w, e, rfl, hw, hproj, hcoef, ?_, he⟩
  have hre := localRadialDerivative_representative μ hQ Ω (T₂.replacement i) w hf
  rw [hid] at hre
  exact hre.symm.trans (SobolevSpace.restrictLp_coe μ hQ Ω _)

end RegularPointCoordinates

end

end OAI
