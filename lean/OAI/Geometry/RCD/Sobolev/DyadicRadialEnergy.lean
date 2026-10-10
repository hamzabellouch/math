import OAI.Geometry.RCD.Harmonic.DyadicCenteredRadial
import OAI.Geometry.RCD.Coordinates.FramedRadialEnergy
import OAI.Geometry.RCD.Sobolev.CenteredAffineSobolev
import OAI.Geometry.RCD.Coordinates.NormalizedFitEnergy
import OAI.Geometry.RCD.Sobolev.RadialEnergyVolume
import OAI.Geometry.RCD.Coordinates.FramedRadialValue
import OAI.Geometry.RCD.Harmonic.RadialValueVolume

namespace OAI

/-! # All-scale scalar radial value and energy estimates -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The same centered affine fit controls values of the genuine distance
radial derivative and gradients of its genuine Poisson counterpart.
Both errors use the same summable Poisson envelope and the same frame. -/
theorem dyadic_radial_value_energy {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [IsFiniteMeasureOnCompacts (hausdorff (m + 2) X)]
    (hhessian : LocalPoissonHessianInput hX)
    {a κ r0 B J C A Cχ L δ : ℝ} {p : X}
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hCχ : 0 ≤ Cχ)
    (hr01 : r0 ≤ 1) (hscale : a * (3 * r0) ≤ 1)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ p r0)
    (T : DyadicDistanceReplacements (hausdorff (m + 2) X) hX.quadratic S B J C)
    (hP : Summable (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S))
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ r0 →
      |(hausdorff (m + 2) X).real (ball p t) / (euclideanUnitVolume (m + 2) * t ^ (m + 2)) - 1| ≤ 1 / 4)
    (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
    (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (F : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2))
    (v : ℕ → X → Euclidean (m + 2)) (hδ : 0 ≤ δ)
    (hδ1 : radialNormalizationRestrictionConstant (m + 2) * δ ≤ 1)
    (hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * δ) ≤ 1 / 64)
    (hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
      (ball p (2 * distanceSourceRadius r0 i)) measurableSet_ball (F i))
    (hfirst : ∀ i, FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p
      (2 * distanceSourceRadius r0 i) δ (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (F i)) (v i))
    (hmetric : ∀ i, IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v i x - v i p)))
    (hf : ∀ i, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : ∀ i, GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    {d : ℕ} (hd : 0 < d)
    (hfit : ∀ i, HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ d))
    (hmean : LocalHarmonicL2MeanValueInput hX) {κ₀ ε : ℝ} (hκ₀ : 0 ≤ κ₀)
    (V : X → Euclidean (m + 2))
    (hu : FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p r0 ε u V)
    (hcurv : ∀ i, -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2)
    (hgradient : LocalHarmonicL2GradientInput hX) :
    ∃ Cg D : ℝ, 1 ≤ Cg ∧ 0 < D ∧ ∀ b : Euclidean (m + 2), b ≠ 0 →
      ∃ coeff : ℕ → Euclidean (m + 2),
      ∃ g : ℕ → SobolevSpace (hausdorff (m + 2) X) hX.quadratic,
      ∀ i,
      let μ := hausdorff (m + 2) X
      let s := distanceSourceRadius r0 i
      let r := s / 64
      let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
        (normalizedPoissonDefect μ hX.quadratic S) i
      let H := centeredAffineSobolev μ hX.quadratic u (χ i).sobolev (V p) (coeff i)
      (SobolevSpace.toLp μ hX.quadratic (g i) =ᵐ[μ.restrict (ball p r)]
        localGamma μ hX.quadratic (T.replacement i) (sobolevColumnMap μ hX.quadratic u b)) ∧
      ‖normalizeLocalL2 μ (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (dyadicRadialTarget hX T u hbase i b - SobolevSpace.restrictLp μ hX.quadratic (ball p r) H)‖ ≤
        D * r * ‖(F i).symm b‖ * Real.sqrt E ∧
      ‖normalizeLocalL2 μ (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic (ball p r) (g i - H))‖ ^ 2 ≤
        (2 * D ^ 2 + 8192 * (((m + 2 : ℕ) : ℝ) * 2) ^ 2 * B *
          ((4 / (3 * euclideanUnitVolume (m + 2))) * (64 : ℝ) ^ (m + 2))) *
          (r * ‖(F i).symm b‖) ^ 2 * E ∧
      (μ.real (ball p (r / 2)))⁻¹ *
        (∫ x in ball p (r / 2), localGamma μ hX.quadratic (g i - H) (g i - H) x ∂μ) ≤
        radialEnergyConstant K (m + 2) Cg 1 A B J Cχ *
          ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ (m + 2))⁻¹ * D ^ 2 +
            (4 / (3 * euclideanUnitVolume (m + 2))) * (128 : ℝ) ^ (m + 2)) *
          ‖(F i).symm b‖ ^ 2 * E := by
  let μ := hausdorff (m + 2) X
  let hQ := hX.quadratic
  let r : ℕ → ℝ := fun i => distanceSourceRadius r0 i / 64
  let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
    (normalizedPoissonDefect μ hQ S)
  have hr (i : ℕ) : 0 < r i := div_pos (distanceSourceRadius_pos S.radius_pos i) (by norm_num)
  have hrr (i : ℕ) : r i ≤ r0 := by
    have h := distanceSourceRadius_outer_le S.radius_pos.le i
    have hs := distanceSourceRadius_pos S.radius_pos i
    dsimp only [r]; linarith
  have hsub (i : ℕ) : ball p (r i) ⊆ ball p r0 := ball_subset_ball (hrr i)
  have hδle : δ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (radialNormalizationRestrictionConstant_ge_one (m + 2)) hδ
    linarith
  have hnormalized (i : ℕ) := (hfirst i).mono_error μ hQ hδ hδle
  obtain ⟨Cg, hCg, henergy⟩ := framed_radial_fit_energy hX hhessian hgradient (by omega) hκ₀
  obtain ⟨D, hD, hfits⟩ := dyadic_centered_radial_estimate m hX hhessian ha hκ hK hB hJ hA hCχ
    hr01 hscale hBG S T hP hquarter u hbase F v hδ hδ1 hsmall hexact hfirst hmetric hf χ hd hfit
    hmean hκ₀ V hu hcurv
  obtain ⟨_hEs, _hEsum, hEN⟩ := radial_fit_pinching_envelope_budget S hκ hCχ hδ hP
  refine ⟨Cg, D, hCg, hD, ?_⟩
  intro b hb
  obtain ⟨_c, coeff, _hfit, _hcenter, hvalues⟩ := hfits b hb
  have hpair (i : ℕ) :
      ∃ G : LocalHessianPairing μ hQ (ball p (r i)) (T.replacement i) (sobolevColumnMap μ hQ u b),
      ∀ (H : SobolevSpace μ hQ) {I : ℝ}, IsSobolevHarmonicOn μ hQ (ball p (r i)) H →
      ‖dyadicRadialTarget hX T u hbase i b - SobolevSpace.restrictLp μ hQ (ball p (r i)) H‖ ^ 2 ≤ I →
      (∫ x in ball p (r i / 2), localGamma μ hQ (G.mixed - H) (G.mixed - H) x ∂μ) ≤
        radialEnergyConstant K (m + 2) Cg 1 A B J Cχ *
          (I / (r i) ^ 2 + (distanceSourceRadius r0 i ^ ((m + 2 : ℕ) : ℝ) *
            normalizedPoissonDefect μ hQ S i) * ‖(F i).symm b‖ ^ 2) := by
    have hs := distanceSourceRadius_pos S.radius_pos i
    have hsle : distanceSourceRadius r0 i ≤ r0 := by
      have hh := distanceSourceRadius_outer_le S.radius_pos.le i
      linarith
    have hsubN : ball p (distanceSourceRadius r0 i / 4) ⊆
        ball p (2 * distanceSourceRadius r0 i) := ball_subset_ball (by linarith)
    have hann := relative_volume_annulus (show 2 ≤ m + 2 by omega) (hr i)
      (euclideanUnitVolume_pos (m + 2)) (hquarter _ (hr i) (hrr i))
      (hquarter (2 * r i) (by positivity) (by dsimp only [r]; linarith))
    simpa only [dyadicRadialTarget, r] using henergy hκ hK hB hJ hA (by norm_num : (0 : ℝ) ≤ 1) hCχ p S T i
      (hsle.trans hr01) (hcurv i) u (F i)
      (fun j => ((hnormalized i).harmonic j).mono μ hQ hsubN)
      (fun j => ae_restrict_of_ae_restrict_of_subset hsubN ((hnormalized i).gradient j))
      (hf i) (χ i) hann.1 hann.2 (hbase i) b
  choose G hG using hpair
  refine ⟨coeff, fun i => (G i).mixed, ?_⟩
  intro i
  have hri : 0 < r i := hr i
  have hω : 0 < euclideanUnitVolume (m + 2) := euclideanUnitVolume_pos (m + 2)
  dsimp only
  let s := distanceSourceRadius r0 i
  let H := centeredAffineSobolev μ hQ u (χ i).sobolev (V p) (coeff i)
  have hη : SobolevSpace.restrictLp μ hQ (ball p (r i)) (χ i).sobolev =
      restrictedOne μ (ball p (r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) := by
    apply restrictLp_eq_one_of_representative
    filter_upwards [ae_restrict_of_ae (χ i).representative, ae_restrict_mem measurableSet_ball]
      with x hx hxr
    exact hx.trans ((χ i).one x hxr)
  have hrestrict := centeredAffineSobolev_restrict μ hQ u (χ i).sobolev (V p) (coeff i)
    (ball p (r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hη
  have hH : IsSobolevHarmonicOn μ hQ (ball p (r i)) H :=
    centeredAffineSobolev_harmonic μ hQ u (χ i).sobolev (V p) (coeff i) _
      (fun j => (hu.harmonic j).mono μ hQ (hsub i)) ((χ i).harmonic_on_inner_ball μ hQ)
  have hnorm : ‖normalizeLocalL2 μ (ball p (r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (dyadicRadialTarget hX T u hbase i b - SobolevSpace.restrictLp μ hQ (ball p (r i)) H)‖ ≤
      D * r i * ‖(F i).symm b‖ * Real.sqrt (E i) := by
    rw [hrestrict]
    exact hvalues i
  refine ⟨(G i).mixed_rep, hnorm, ?_, ?_⟩
  · have hI := norm_sq_le_of_normalized_fit μ (ball p (r i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (ne_of_gt (hX.fullSupport p _ (hr i)))
      _ (by positivity : 0 ≤ D * r i * ‖(F i).symm b‖ * Real.sqrt (E i)) hnorm
    have hgrad (j : Fin (m + 2)) : ∀ᵐ x ∂μ.restrict (ball p (r i)),
        localGamma μ hQ (transformedColumn μ hQ u (F i) j)
          (transformedColumn μ hQ u (F i) j) x ≤ (2 : ℝ) ^ 2 := by
      have hsubN : ball p (r i) ⊆ ball p (2 * s) := by
        apply ball_subset_ball
        dsimp only [r, s]
        linarith [distanceSourceRadius_pos S.radius_pos i]
      simpa only [one_add_one_eq_two] using
        ae_restrict_of_ae_restrict_of_subset hsubN ((hnormalized i).gradient j)
    have hvalue := T.framed_value_transfer μ hQ i u (F i) hgrad b (G i) H (hbase i) hI
    have houter := hquarter (r i) (hr i) (hrr i)
    have hV := (quarter_volume_bounds (hr i) hω houter).1
    have hN := radial_testing_volume_ratio (distanceSourceRadius_pos S.radius_pos i) hω houter
    have hmass : (S.source i).real (ball p s) ≤ s ^ ((m + 2 : ℕ) : ℝ) *
        normalizedPoissonDefect μ hQ S i := by
      rw [normalizedPoissonDefect_units]
      have hn : 0 ≤ κ * s ^ 2 * μ.real (ball p s) := by positivity
      exact le_add_of_nonneg_right hn
    have hMP : (S.source i).real (ball p s) / μ.real (ball p (r i)) ≤
        ((4 / (3 * euclideanUnitVolume (m + 2))) * (64 : ℝ) ^ (m + 2)) * E i := by
      calc
        _ ≤ (s ^ ((m + 2 : ℕ) : ℝ) * normalizedPoissonDefect μ hQ S i) /
            μ.real (ball p (r i)) := div_le_div_of_nonneg_right hmass hV.le
        _ = (s ^ ((m + 2 : ℕ) : ℝ) / μ.real (ball p (r i))) *
            normalizedPoissonDefect μ hQ S i := by ring
        _ ≤ _ := mul_le_mul hN (hEN i).2
          (normalizedPoissonDefect_nonneg μ hQ S hκ i) (by positivity)
    have hsr : 64 * r i = distanceSourceRadius r0 i := by dsimp only [r]; ring
    have hh := radial_fit_value_volume_units (r := r i) hV
      (sq_nonneg (((m + 2 : ℕ) : ℝ) * 2)) hB (hEN i).1 hMP
      (by simpa only [hsr] using hvalue)
    rw [normalizeLocalL2_norm_sq, ← l2_norm_sq_eq_integral]
    exact hh
  have hI := norm_sq_le_of_normalized_fit μ (ball p (r i))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (ne_of_gt (hX.fullSupport p _ (hr i)))
    _ (by positivity : 0 ≤ D * r i * ‖(F i).symm b‖ * Real.sqrt (E i)) hnorm
  have he := hG i H hH hI
  have hW : 0 < μ.real (ball p (r i / 2)) := ENNReal.toReal_pos
    (ne_of_gt (hX.fullSupport p _ (by positivity))) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hinnerle : r i / 2 ≤ r0 := (by linarith [hrr i, hr i])
  have houter := hquarter (r i) (hr i) (hrr i)
  have hinner := hquarter (r i / 2) (by positivity) hinnerle
  have hratio := radial_fraction_volume_ratio (hr i) (by norm_num : (0 : ℝ) < 1 / 2)
    (euclideanUnitVolume_pos (m + 2)) houter
    (by simpa only [show (1 / 2 : ℝ) * r i = r i / 2 by ring] using hinner)
  have hNratio : s ^ ((m + 2 : ℕ) : ℝ) / μ.real (ball p (r i / 2)) ≤
      (4 / (3 * euclideanUnitVolume (m + 2))) * (128 : ℝ) ^ (m + 2) := by
    obtain ⟨_, hlo, _⟩ := quarter_volume_bounds (by positivity : 0 < r i / 2)
      (euclideanUnitVolume_pos (m + 2)) hinner
    apply (div_le_iff₀ hW).mpr
    have heq : (4 / (3 * euclideanUnitVolume (m + 2))) * (128 : ℝ) ^ (m + 2) *
        ((3 / 4 : ℝ) * euclideanUnitVolume (m + 2) * (r i / 2) ^ (m + 2)) = s ^ ((m + 2 : ℕ) : ℝ) := by
      have hri : r i / 2 = s / 128 := by dsimp only [r, s]; ring
      rw [hri, Real.rpow_natCast, div_pow]
      field_simp [(euclideanUnitVolume_pos (m + 2)).ne']
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hlo (by positivity)
  exact radial_fit_energy_volume_units (hr i) hW (Real.rpow_nonneg (distanceSourceRadius_pos S.radius_pos i).le _)
    (radialEnergyConstant_pos (G := Cg) (ε := 1) (A := A) hB hJ hCχ).le
    (hEN i).1 (hEN i).2 hratio hNratio he

end RegularPointCoordinates

end

end OAI
