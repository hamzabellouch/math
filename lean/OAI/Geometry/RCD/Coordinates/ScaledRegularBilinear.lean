import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularNeighborhoodHeat
import OAI.Geometry.RCD.Heat.ScaledHeatControls
import OAI.Geometry.RCD.Sobolev.ScaledFixedCutoffNeighborhood
import OAI.Geometry.RCD.Harmonic.ScaledNeighborhoodGram
import OAI.Geometry.RCD.Harmonic.ScaledHarmonicMass
import OAI.Geometry.RCD.Heat.ScaledHeatBase
import OAI.Geometry.RCD.Sobolev.HarmonicEnergyBound
import OAI.Geometry.RCD.Harmonic.NeighborhoodGramEnvelope
import OAI.Geometry.RCD.Heat.EventualEnvelopeOrder
import OAI.Geometry.RCD.Harmonic.ContinuousAffineImprovement

namespace OAI

/-! # The bilinear and cumulative heat estimates for the same regular-point data -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Published normalization, Bochner and kernel inputs produce both the actual
bilinear comparison and the three cumulative estimates with one common family. -/
theorem scaled_regular_neighborhood_bilinear_heat {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 2) X) (m + 2) p)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    :
    ∃ d : ℕ, 3 ≤ d ∧ ∀ enlargement : ℝ, 0 ≤ enlargement →
    ∃ (J : ℕ) (A B D H : ℝ), 0 < A ∧ 0 < B ∧ 0 < D ∧ 0 < H ∧
    ∀ {radiusCap ζ : ℝ}, 0 < radiusCap → 0 < ζ →
    ∃ R : ℝ, ∃ hR : 0 < R, ∃ _hRcap : R ≤ radiusCap, ∃ lambda : ℝ, ∃ hlambda : 0 < lambda,
    ∃ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
      (v : X → Euclidean (m + 2)) (e : ℝ)
      (M : PositiveBilinearMeasure X (Euclidean (m + 2))) (Ccut : ℝ)
      (χ : GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (3 * R / 8) Ccut)
      (L : ℝ≥0),
      R ≤ 1 ∧ lambda * R ^ 2 = 8 * ((m + 2 : ℕ) : ℝ) ^ 2 + 2 ∧
      |K| * R ^ 2 ≤ ζ ∧ 0 < e ∧ e ≤ 1 ∧
      FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p (32 * R) e u v ∧
      (L : ℝ) ^ 2 ≤ 4 * ((m + 2 : ℕ) : ℝ) ^ 2 ∧
      (∀ z, Nonempty (LocalHarmonicEnergy (hausdorff (m + 2) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) M |K| p (4 * R) L z)) ∧
      ∀ q ∈ ball p (R / 32),
        let Q := dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ q hR hlambda
        ((∀ v, ‖v‖ ^ 2 ≤ 2 * ⟪v, sobolevMeanGram (hausdorff (m + 2) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
            (ball q R) measurableSet_ball v⟫_ℝ) ∧
          (∀ i, J ≤ i → ∀ v,
            (1 - 1 / 64 : ℝ) * ⟪v, sobolevMeanGram (hausdorff (m + 2) X) hX.quadratic
              (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
              (ball q (R / 2 ^ i)) measurableSet_ball v⟫_ℝ ≤ ⟪v, Q i v⟫_ℝ ∧
            ⟪v, Q i v⟫_ℝ ≤ (1 + 1 / 64 : ℝ) *
              ⟪v, sobolevMeanGram (hausdorff (m + 2) X) hX.quadratic
                (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
                (ball q (R / 2 ^ i)) measurableSet_ball v⟫_ℝ) ∧
          (∀ i, J ≤ i → ∀ v,
            ⟪v, Q (i + 1) v⟫_ℝ ≤ ⟪v, Q i v⟫_ℝ ∧
            ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ)) ∧
        (∀ (xi : Euclidean (m + 2)) (k : ℕ),
          let h := ⟪xi, (Q (J + k)).symm xi⟫_ℝ
          let mass := ∑ i ∈ Finset.range k,
            ⟪(Q (J + i)).symm xi, dyadicBochnerMass M (m + 2) q R (J + i) ((Q (J + i)).symm xi)⟫_ℝ
          (∑ i ∈ Finset.range k,
            ⟪(Q (J + i)).symm xi, dyadicBochnerEnvelope M (m + 2) q R (J + i) ((Q (J + i)).symm xi)⟫_ℝ) ≤ A * h ∧
          ‖xi‖ ^ 2 + mass ≤ B * h ∧ h ≤ D * (‖xi‖ ^ 2 + mass)) ∧
        (∀ i, J ≤ i → ∀ y, dist q y ≤ enlargement * (R / 2 ^ i) →
          ∀ b w : Euclidean (m + 2),
          ⟪b, (sobolevMeanGram (hausdorff (m + 2) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
            (ball y (R / 2 ^ i)) measurableSet_ball - (Q i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))) w⟫_ℝ ^ 2 ≤
              H * ⟪b, Q i b⟫_ℝ * ⟪w, dyadicBochnerEnvelope M (m + 2) q R i w⟫_ℝ) ∧
        (∀ r : ℝ, 0 < r → r ≤ R / 16 →
          HasNormalizedAffineImprovement hX u q r ((1 / 2 : ℝ) ^ d)) ∧
        ∃ S : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2),
          (∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
            (ball q (R / 2 ^ i)) measurableSet_ball (S i)) ∧
          (∀ i, FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic q (R / 2 ^ i) ζ
            (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (S i))
            (fun x => (S i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (v x))) ∧
          ∀ i, IsPointedApproximation q 0 ((R / 2 ^ i) / 128) 4 ζ
            (fun x => ((R / 2 ^ i) / 128)⁻¹ •
              ((S i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (v x) -
                (S i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (v q))) := by
  classical
  let μ := hausdorff (m + 2) X
  let omega := euclideanUnitVolume (m + 2)
  have homega : 0 < omega := euclideanUnitVolume_pos _
  let Lambda := 8 * ((m + 2 : ℕ) : ℝ) ^ 2 + 2
  have hLambda : 0 < Lambda := by dsimp only [Lambda]; positivity
  let L : ℝ≥0 := ⟨2 * ((m + 2 : ℕ) : ℝ), by positivity⟩
  have hLeq : (L : ℝ) ^ 2 = 4 * ((m + 2 : ℕ) : ℝ) ^ 2 := by
    change (2 * ((m + 2 : ℕ) : ℝ)) ^ 2 = _
    ring
  obtain ⟨Ccut, Dsource, hCcut, hDsource, hcut, J₀, hcutoffBuild⟩ :=
    exists_scaled_fixed_cutoff_neighborhood_with_source hX (by omega)
      hhessian hproduct hcutoff hk hg homega
  have hVlo : 0 < omega / (2 * (2 : ℝ) ^ (m + 2)) := by positivity
  have hVhi : 0 < (3 / 2 : ℝ) * omega := by positivity
  obtain ⟨d, hd, δ, hδ, hδ1, haffine⟩ := affine_improvement_from_continuous_coordinates
    hX (by omega) hharmonic hgradient heuclidean hmetricmeasure
  obtain ⟨ε, εmass, C, N, hε, hε1, hεmass, hC, habsorb, hcontrols⟩ :=
    scaled_heat_controls_at_of_splitting m hX ha hBG hk hg
      (L := 4 * ((m + 2 : ℕ) : ℝ) ^ 2) (B := 2) (C := Ccut) (Lambda := Lambda + 1)
      (by positivity) (by norm_num) hVlo hVhi (zero_le_one.trans hCcut) (by positivity)
  refine ⟨d, hd, ?_⟩
  intro enlargement henlargement
  obtain ⟨Cg, hCg, Jg, hgramBuild⟩ := exists_scaled_neighborhood_gram_envelope_bound
    μ hX.quadratic hk m hg hdiff homega henlargement
    (show 0 ≤ 4 * ((m + 2 : ℕ) : ℝ) ^ 2 by positivity) hDsource hLambda.le
  let J := max Jg (max 4 (max N J₀))
  let Dmass := ((Ccut / 8 + 1) * (4 * ((m + 2 : ℕ) : ℝ) ^ 2) *
    (3 / 2 * omega) * 5 ^ (m + 2))
  have hDmass : 0 ≤ Dmass := by dsimp only [Dmass]; positivity
  obtain ⟨b, hb, hbackgroundBuild⟩ := exists_scaled_mass_background (X := X)
    (E := Euclidean (m + 2)) (m + 2) J hDmass
  obtain ⟨T, hT, hbaseBuild⟩ := exists_scaled_dyadic_heat_base μ hX.quadratic hk (m + 2) J
    hLambda (show 0 ≤ 4 * ((m + 2 : ℕ) : ℝ) ^ 2 by positivity)
  obtain ⟨A, B, D, hA, hB, hD, hresult⟩ :=
    exists_uniform_heat_cumulative_constants (E := Euclidean (m + 2)) hb hT hεmass hC habsorb
  let H := Cg ^ 2 * (b * T + 8 * εmass)
  have hH : 0 < H := by
    have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
    dsimp only [H]
    positivity
  refine ⟨J, A, B, D, H, hA, hB, hD, hH, ?_⟩
  intro radiusCap ζ hRadiusCap hζ
  let β := min ε (min δ ζ)
  let ρ := min (δ / 4) (ζ / 8)
  have hβ : 0 < β := lt_min hε (lt_min hδ hζ)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hβε : β ≤ ε := min_le_left _ _
  have hβδ : β ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hβζ : β ≤ ζ := (min_le_right _ _).trans (min_le_right _ _)
  have hρδ : 4 * ρ ≤ δ := by have hh := min_le_left (δ / 4) (ζ / 8); dsimp only [ρ]; linarith
  have hρζ : 8 * ρ ≤ ζ := by have hh := min_le_right (δ / 4) (ζ / 8); dsimp only [ρ]; linarith
  obtain ⟨R, e, hR, hRcap, hRsmall, hscale, hcurv, he, he1, L₀, u, v, M, hL₀, hu, hG, hvol, hfamily, hmetric⟩ :=
    regular_uniform_dyadic_data_with_cap (ρ := ρ) (β := β) (m + 1) hX (by omega) ha hcompact hregular hvolume hmeasured hBG
      hdensity hinitial htrans hsplit hrigidity hbochner hRadiusCap hρ hβ
  have hcurvδ : |K| * (16 * R) ^ 2 ≤ δ := hcurv.trans hβδ
  have hcurvζ : |K| * R ^ 2 ≤ ζ := by
    have hh := mul_le_mul_of_nonneg_left
      (show R ^ 2 ≤ (16 * R) ^ 2 by nlinarith only [sq_nonneg R]) (abs_nonneg K)
    exact hh.trans (hcurv.trans hβζ)
  have hcurv : |K| * (16 * R) ^ 2 ≤ ε := hcurv.trans hβε
  have hR1 : R ≤ 1 := by linarith only [hRsmall]
  have hscale' : a * (3 * R) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (show 3 * R ≤ 48 * R by linarith only [hR]) ha
    linarith only [hscale, hh]
  have hcurv' : |K| * R ^ 2 ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left
      (show R ^ 2 ≤ (16 * R) ^ 2 by nlinarith only [sq_nonneg R]) (abs_nonneg K)
    exact hh.trans hcurv
  let lambda := Lambda / R ^ 2
  have hlambda : 0 < lambda := div_pos hLambda (sq_pos_of_pos hR)
  have hlambdaScale : lambda * R ^ 2 = Lambda := by dsimp only [lambda]; field_simp
  have hlambdaAbs : |lambda| * R ^ 2 ≤ Lambda := by rw [abs_of_pos hlambda, hlambdaScale]
  have hlambdaSum : (lambda + (R ^ 2)⁻¹) * R ^ 2 ≤ Lambda + 1 := by
    rw [add_mul, hlambdaScale, inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos hR))]
  have hL : (L : ℝ) ^ 2 ≤ 4 * ((m + 2 : ℕ) : ℝ) ^ 2 := hLeq.le
  have hcurv1 : |K| * (16 * R) ^ 2 ≤ 1 := hcurv.trans hε1
  have hcurvR : |K| * R ^ 2 ≤ 1 := hcurv'.trans hε1
  have hreg : 2 * |K| * (L : ℝ) ^ 2 + (R ^ 2)⁻¹ ≤ lambda := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    rw [add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos hR)), hLeq]
    have hh := mul_le_mul_of_nonneg_left hcurvR
      (show 0 ≤ 8 * ((m + 2 : ℕ) : ℝ) ^ 2 by positivity)
    dsimp only [Lambda]
    nlinarith only [hh]
  let G := fun z => (Classical.choice (hG z)).enlargeBound μ hX.quadratic (hL₀.trans_eq hLeq.symm)
  have hgradient32 : ∀ z : Euclidean (m + 2), ∀ᵐ x ∂μ.restrict (ball p (32 * R)),
      localGamma μ hX.quadratic (sobolevColumnMap μ hX.quadratic u z)
        (sobolevColumnMap μ hX.quadratic u z) x ≤ (L : ℝ) ^ 2 * ‖z‖ ^ 2 := by
    intro z
    have hc : (((m + 2 : ℕ) : ℝ) * (1 + e)) ^ 2 ≤ (L : ℝ) ^ 2 := by
      rw [hLeq]
      have he' : (1 + e) ^ 2 ≤ 4 := by nlinarith only [he, he1]
      nlinarith only [mul_le_mul_of_nonneg_left he' (sq_nonneg (((m + 2 : ℕ) : ℝ)))]
    filter_upwards [hu.directional_gradient μ hX.quadratic z] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z‖))
  obtain ⟨χ, hsourceL1, hχ⟩ := hcutoffBuild R hR hR1 hcurv1 p L u M hL
    hu.harmonic hgradient32 hvol G
  have hgram := hgramBuild R hR hR1 (sobolevColumnMap μ hX.quadratic u) M |K| p L G Ccut χ
    hL (by simpa only [abs_abs] using hcurvR) hsourceL1 lambda hlambdaAbs hvol
  have hKR2 : -1 ≤ K * (2 * R) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (2 * R))
    have hh' := mul_nonneg (abs_nonneg K) (sq_nonneg R)
    nlinarith only [hh, hh', hcurv1]
  obtain ⟨ψ⟩ := hcut p (2 * R) (by positivity) hKR2
  have hv5 : μ.real (closedBall p (4 * R)) ≤ (3 / 2 * omega) * (5 * R) ^ (m + 2) := by
    apply (measureReal_mono (closedBall_subset_ball (show 4 * R < 5 * R by linarith only [hR]))
      (hX.finiteOnBounded _ isBounded_ball).ne).trans
    have hv := (abs_le.mp (hvol p (by simp; positivity) (5 * R) (by positivity) (by linarith only [hR]))).2
    have hd : 0 < omega * (5 * R) ^ (m + 2) := by positivity
    have hratio : μ.real (ball p (5 * R)) / (omega * (5 * R) ^ (m + 2)) ≤ 3 / 2 := by linarith only [hv]
    have hh := (div_le_iff₀ hd).mp hratio
    nlinarith only [hh]
  have hlocal : ∀ z, ⟪z, M.massOperator (ball p (2 * R)) z⟫_ℝ ≤
      Dmass * (R ^ (m + 2) / R ^ 2) * ‖z‖ ^ 2 :=
    harmonic_scaled_local_mass_bound μ hX.quadratic hR (abs_nonneg K)
      (zero_le_one.trans hCcut) (by positivity) hcurvR _ M L G ψ hL hv5
  have hbackground := hbackgroundBuild R hR p M hlocal
  have hbase := hbaseBuild R hR _ M |K| (4 * R) (3 * R / 8) Ccut p L G χ (by linarith only [hR]) hL
  refine ⟨R, hR, hRcap, lambda, hlambda, u, v, e, M, Ccut, χ, L,
    hR1, hlambdaScale, hcurvζ, he, he1, hu, hL, (fun z => ⟨G z⟩), ?_⟩
  intro q hq
  have hqp : dist q p < R / 32 := hq
  have hqR : q ∈ ball p R := by change dist q p < R; linarith only [hqp, hR]
  obtain ⟨S, hexact, hfirst, hS0, hfirstv, hmetricS⟩ := hfamily q hqR
  have hfirst' (i : ℕ) : ∃ w : X → Euclidean (m + 2),
      FirstOrderSplittingOn μ hX.quadratic q (R / 2 ^ i) ε
        (transformedColumn μ hX.quadratic u (S i)) w := by
    obtain ⟨w, hw⟩ := hfirst i
    exact ⟨w, hw.mono_error μ hX.quadratic hβ.le hβε⟩
  have hsub : ball q (2 * (2 * R)) ⊆ ball p (2 * (4 * R)) := by
    intro x hx
    have hxq : dist x q < 2 * (2 * R) := hx
    change dist x p < 2 * (4 * R)
    have hh := dist_triangle x q p
    linarith only [hh, hxq, hqp, hR]
  let Gq := fun z => (G z).restrict μ hX.quadratic hsub
  have hvolq : ∀ y, dist q y ≤ 2 * R → ∀ s, 0 < s → s ≤ R →
      |μ.real (ball y s) / (omega * s ^ (m + 2)) - 1| ≤ 1 / 2 := by
    intro y hy s hs hsR
    apply hvol y ?_ s hs (by linarith only [hsR, hR])
    have hh := dist_triangle p q y
    rw [dist_comm p q] at hh
    linarith only [hh, hqp, hy, hR]
  have hgradient : ∀ z : Euclidean (m + 2), ∀ᵐ x ∂μ.restrict (ball q R),
      localGamma μ hX.quadratic (sobolevColumnMap μ hX.quadratic u z)
        (sobolevColumnMap μ hX.quadratic u z) x ≤
          (4 * ((m + 2 : ℕ) : ℝ) ^ 2) * ‖z‖ ^ 2 := by
    intro z
    filter_upwards [LocalHarmonicEnergy.gamma_bound_on_smaller_ball μ hX.quadratic Gq
      (show R ≤ 2 * (2 * R) by linarith only [hR]) z] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right hL (sq_nonneg _))
  have hc := hcontrols R hR hR1 hscale' lambda (R ^ 2)⁻¹ hlambda (by positivity) hlambdaSum u M S q ε L Gq hε.le le_rfl hcurv' hreg hS0
    hexact hfirst' (hcut q) (dyadic_heat_volumes_of_common_regime μ (m + 2) q hR homega hvolq)
    hgradient p (4 * R) (3 * R / 8) Ccut G χ (by positivity) (by linarith only [hR])
    (hχ q hq).1 (hχ q hq).2.1 J₀ (hχ q hq).2.2 J (le_max_right _ _)
  let Q := dyadicHeatGramAt μ hX.quadratic hk (sobolevColumnMap μ hX.quadratic u) χ q hR hlambda
  have horder (i : ℕ) (hi : J ≤ i) (v : Euclidean (m + 2)) :
      ⟪v, Q (i + 1) v⟫_ℝ ≤ ⟪v, Q i v⟫_ℝ ∧
      ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ := by
    have hd := (hc.1.decrement i hi v).1
    simp only [sub_apply, inner_sub_right] at hd
    change 0 ≤ ⟪v, Q i v⟫_ℝ - ⟪v, Q (i + 1) v⟫_ℝ at hd
    exact ⟨sub_nonneg.mp hd, hc.1.step i hi v⟩
  refine ⟨⟨?_, hc.2, horder⟩, ?_, ?_, ?_, S, hexact, ?_, ?_⟩
  · intro v
    have h := norm_apply_sq_le_of_norm_sq_le
      (S 0 : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)) hS0 ((S 0).symm v)
    have he := meanGram_energy_of_exact_normalization μ hX.quadratic
      (sobolevColumnMap μ hX.quadratic u) (ball q R) measurableSet_ball (S 0)
      (by simpa only [pow_zero, div_one] using hexact 0) v
    change ‖v‖ ^ 2 ≤ 2 * ⟪v, sobolevMeanGram μ hX.quadratic
      (sobolevColumnMap μ hX.quadratic u) (ball q R) measurableSet_ball v⟫_ℝ
    rw [he]
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h
  · apply hresult Q (dyadicBochnerMass M (m + 2) q R) (dyadicBochnerEnvelope M (m + 2) q R) J
      (dyadicHeatGramAt_isPositive μ hX.quadratic hk _ χ q hR hlambda)
      (dyadicBochnerMass_isPositive M (m + 2) q hR.le) hc.1.step hc.1.decrement hc.1.small
      (hbackground q hqR)
    · exact fun z => (hbase q z).1
    · exact fun z => (hbase q z).2

  · intro i hi y hy v w
    have hpos (j : ℕ) : (Q j : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).IsPositive :=
      dyadicHeatGramAt_isPositive μ hX.quadratic hk _ χ q hR hlambda j
    have hcurrent (z : Euclidean (m + 2)) :
        ⟪z, dyadicBochnerEnvelope M (m + 2) q R i z⟫_ℝ ≤
          (b * T + 8 * εmass) * ⟪z, Q i z⟫_ℝ := by
      have h := hc.1.envelope_le_current hpos hεmass (zero_le_one.trans hb) hT.le
        (fun z => (hbase q z).2) (hbackground q hqR) (i - J) z
      simpa only [Nat.add_sub_of_le hi] using h
    have hsource (z : Euclidean (m + 2)) :
        |⟪z, (sobolevMeanGram μ hX.quadratic (sobolevColumnMap μ hX.quadratic u)
          (ball y (R / 2 ^ i)) measurableSet_ball - (Q i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))) z⟫_ℝ| ≤
            Cg * ⟪z, dyadicBochnerEnvelope M (m + 2) q R i z⟫_ℝ := by
      simpa only [Q, dyadicHeatGramAt_coe] using
        hgram i ((le_max_left _ _).trans hi) q hq y hy z
    have hsym := (sobolevMeanGram_isPositive μ hX.quadratic
      (sobolevColumnMap μ hX.quadratic u) (ball y (R / 2 ^ i)) measurableSet_ball).isSymmetric.sub
        (hpos i).isSymmetric
    exact bilinear_heat_comparison_of_envelope (Q i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))
      (dyadicBochnerEnvelope M (m + 2) q R i) _
      (dyadicBochnerEnvelope_isPositive M (m + 2) q hR.le i) hsym hsource hcurrent v w

  · intro r hr hrR
    have hsubr : ball q r ⊆ ball p (32 * R) := by
      intro x hx
      have hh := dist_triangle x q p
      have hxq : dist x q < r := hx
      change dist x p < 32 * R
      linarith only [hh, hxq, hqp, hrR, hR]
    have hsub4 : ball q (4 * r) ⊆ ball p (32 * R) := by
      intro x hx
      have hh := dist_triangle x q p
      have hxq : dist x q < 4 * r := hx
      change dist x p < 32 * R
      linarith only [hh, hxq, hqp, hrR, hR]
    have hcurvr : -δ ≤ K * r ^ 2 := by
      have hrsq : r ^ 2 ≤ (16 * R) ^ 2 :=
        (sq_le_sq₀ hr.le (by positivity)).mpr (by linarith only [hrR, hR])
      have hh := mul_le_mul_of_nonneg_left hrsq (abs_nonneg K)
      have hk := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)
      linarith only [hh, hk, hcurvδ]
    obtain ⟨N, hN⟩ := hmetric q hqR r hr hrR
    have hN' : IsPointedApproximation q 0 r 2 δ (fun x =>
        (N : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (v x) -
        (N : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (v q)) := by
      exact hN.mono_error hρδ
    have hη : SobolevSpace.toLp μ hX.quadratic χ.sobolev =ᵐ[μ.restrict (ball q r)]
        fun _ => (1 : ℝ) := by
      filter_upwards [ae_restrict_of_ae χ.representative, ae_restrict_mem measurableSet_ball]
        with x hx hxr
      rw [hx]
      apply χ.one x
      have hh := dist_triangle x q p
      have hxq : dist x q < r := hxr
      change dist x p < 3 * R / 8
      linarith only [hh, hxq, hqp, hrR, hR]
    exact haffine q r hr hcurvr u v
      (fun i => ae_restrict_of_ae_restrict_of_subset hsubr (hu.representative i))
      (hu.continuous.mono hsub4) N χ.sobolev hη hN'

  · intro i
    exact (hfirstv i).mono_error μ hX.quadratic hβ.le hβζ
  · intro i
    exact (hmetricS i).mono_error hρζ


end RegularPointCoordinates

end

end OAI
