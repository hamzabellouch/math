import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularNeighborhoodHeat
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
theorem regular_neighborhood_bilinear_heat_with_energy {K : ℝ} (m : ℕ)
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
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    :
    ∃ d : ℕ, 3 ≤ d ∧ ∀ {radiusCap enlargement ζ : ℝ},
    0 < radiusCap → 0 ≤ enlargement → 0 < ζ →
    ∃ R : ℝ, ∃ hR : 0 < R, ∃ _hRcap : R ≤ radiusCap, ∃ lambda : ℝ, ∃ hlambda : 0 < lambda,
    ∃ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
      (v : X → Euclidean (m + 2)) (e : ℝ)
      (M : PositiveBilinearMeasure X (Euclidean (m + 2))) (Ccut : ℝ)
      (χ : GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (3 * R / 8) Ccut)
      (J : ℕ) (A B D H : ℝ) (L : ℝ≥0),
      R ≤ 1 ∧ 0 < A ∧ 0 < B ∧ 0 < D ∧ 0 < H ∧ 0 < e ∧ e ≤ 1 ∧
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
  obtain ⟨Ccut, hCcut, hcut⟩ := hcutoff (by omega)
  let lambda := 8 * |K| * ((m + 2 : ℕ) : ℝ) ^ 2 + 1
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hVlo : 0 < omega / (2 * (2 : ℝ) ^ (m + 2)) := by positivity
  have hVhi : 0 < (3 / 2 : ℝ) * omega := by positivity
  obtain ⟨d, hd, δ, hδ, hδ1, haffine⟩ := affine_improvement_from_continuous_coordinates
    hX (by omega) hharmonic hgradient heuclidean hmetricmeasure
  obtain ⟨ε, εmass, C, N, hε, hε1, hεmass, hC, habsorb, hcontrols⟩ :=
    uniform_heat_controls_at_of_splitting m hX ha hBG hk hg
      (L := 4 * ((m + 2 : ℕ) : ℝ) ^ 2) (B := 2)
      (C := Ccut) (η := 1) (lambda := lambda)
      (by positivity) (by norm_num) hVlo hVhi (by linarith) (by norm_num) hlambda
  refine ⟨d, hd, ?_⟩
  intro radiusCap enlargement ζ hRadiusCap henlargement hζ
  let β := min ε (min δ ζ)
  let ρ := min (δ / 4) (ζ / 8)
  have hβ : 0 < β := lt_min hε (lt_min hδ hζ)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hβε : β ≤ ε := min_le_left _ _
  have hβδ : β ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hβζ : β ≤ ζ := (min_le_right _ _).trans (min_le_right _ _)
  have hρδ : 4 * ρ ≤ δ := by have hh := min_le_left (δ / 4) (ζ / 8); dsimp only [ρ]; linarith
  have hρζ : 8 * ρ ≤ ζ := by have hh := min_le_right (δ / 4) (ζ / 8); dsimp only [ρ]; linarith
  obtain ⟨R, e, hR, hRcap, hRsmall, hscale, hcurv, he, he1, L, u, v, M, hL, hu, hG, hvol, hfamily, hmetric⟩ :=
    regular_uniform_dyadic_data_with_cap (ρ := ρ) (β := β) (m + 1) hX (by omega) ha hcompact hregular hvolume hmeasured hBG
      hdensity hinitial htrans hsplit hrigidity hbochner hRadiusCap hρ hβ
  have hcurvδ : |K| * (16 * R) ^ 2 ≤ δ := hcurv.trans hβδ
  have hcurv : |K| * (16 * R) ^ 2 ≤ ε := hcurv.trans hβε
  have hR1 : R ≤ 1 := by linarith
  have hscale' : a * (3 * R) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (show 3 * R ≤ 48 * R by linarith) ha
    linarith
  have hcurv' : |K| * R ^ 2 ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left
      (show R ^ 2 ≤ (16 * R) ^ 2 by nlinarith [sq_nonneg R]) (abs_nonneg K)
    exact hh.trans hcurv
  have hreg : 2 * |K| * (L : ℝ) ^ 2 + 1 ≤ lambda := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * |K| by positivity)
    dsimp only [lambda]
    nlinarith only [hh]
  let G := fun z => Classical.choice (hG z)
  obtain ⟨χ, J₀, hχ⟩ := exists_fixed_cutoff_neighborhood μ hX.quadratic hk G hg hR homega
    (hcurv.trans hε1) hvol (hcut p)
  obtain ⟨Cg, hCg, Jg, hgram⟩ := exists_neighborhood_gram_envelope_bound μ hX.quadratic hk G χ
    hg hdiff hR hR1 homega hvol henlargement lambda
  let J := max Jg (max 4 (max N J₀))
  obtain ⟨b, hb, hbackground⟩ := exists_uniform_mass_background M (m + 2) hR J
  obtain ⟨T, hT, hbase⟩ := exists_uniform_dyadic_heat_base μ hX.quadratic hk G χ
    (show 3 * R / 8 < 4 * R by linarith) hR hlambda J
  obtain ⟨A, B, D, hA, hB, hD, hresult⟩ :=
    exists_uniform_heat_cumulative_constants (E := Euclidean (m + 2)) hb hT hεmass hC habsorb
  let H := Cg ^ 2 * (b * T + 8 * εmass)
  have hH : 0 < H := by
    have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
    dsimp only [H]
    positivity
  refine ⟨R, hR, hRcap, lambda, hlambda, u, v, e, M, Ccut, χ, J, A, B, D, H, L,
    hR1, hA, hB, hD, hH, he, he1, hu, hL, (fun z => ⟨G z⟩), ?_⟩
  intro q hq
  have hqp : dist q p < R / 32 := hq
  have hqR : q ∈ ball p R := by change dist q p < R; linarith
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
    linarith
  let Gq := fun z => (G z).restrict μ hX.quadratic hsub
  have hvolq : ∀ y, dist q y ≤ 2 * R → ∀ s, 0 < s → s ≤ R →
      |μ.real (ball y s) / (omega * s ^ (m + 2)) - 1| ≤ 1 / 2 := by
    intro y hy s hs hsR
    apply hvol y ?_ s hs (by linarith)
    have hh := dist_triangle p q y
    rw [dist_comm p q] at hh
    linarith
  have hgradient : ∀ z : Euclidean (m + 2), ∀ᵐ x ∂μ.restrict (ball q R),
      localGamma μ hX.quadratic (sobolevColumnMap μ hX.quadratic u z)
        (sobolevColumnMap μ hX.quadratic u z) x ≤
          (4 * ((m + 2 : ℕ) : ℝ) ^ 2) * ‖z‖ ^ 2 := by
    intro z
    filter_upwards [LocalHarmonicEnergy.gamma_bound_on_smaller_ball μ hX.quadratic Gq
      (show R ≤ 2 * (2 * R) by linarith) z] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right hL (sq_nonneg _))
  have hc := hcontrols R hR hR1 hscale' u M S q ε L Gq hε.le le_rfl hcurv' hreg hS0
    hexact hfirst' (hcut q) (dyadic_heat_volumes_of_common_regime μ (m + 2) q hR homega hvolq)
    hgradient p (4 * R) (3 * R / 8) Ccut G χ (by positivity) (by linarith)
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
      (hbackground q)
    · exact fun z => (hbase q z).1
    · exact fun z => (hbase q z).2

  · intro i hi y hy v w
    have hpos (j : ℕ) : (Q j : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).IsPositive :=
      dyadicHeatGramAt_isPositive μ hX.quadratic hk _ χ q hR hlambda j
    have hcurrent (z : Euclidean (m + 2)) :
        ⟪z, dyadicBochnerEnvelope M (m + 2) q R i z⟫_ℝ ≤
          (b * T + 8 * εmass) * ⟪z, Q i z⟫_ℝ := by
      have h := hc.1.envelope_le_current hpos hεmass (zero_le_one.trans hb) hT.le
        (fun z => (hbase q z).2) (hbackground q) (i - J) z
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
      (dyadicBochnerEnvelope M (m + 2) q R i)
      (sobolevMeanGram μ hX.quadratic (sobolevColumnMap μ hX.quadratic u)
        (ball y (R / 2 ^ i)) measurableSet_ball -
        (Q i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)))
      (dyadicBochnerEnvelope_isPositive M (m + 2) q hR.le i) hsym hsource hcurrent v w

  · intro r hr hrR
    have hsubr : ball q r ⊆ ball p (32 * R) := by
      intro x hx
      have hh := dist_triangle x q p
      have hxq : dist x q < r := hx
      change dist x p < 32 * R
      linarith
    have hsub4 : ball q (4 * r) ⊆ ball p (32 * R) := by
      intro x hx
      have hh := dist_triangle x q p
      have hxq : dist x q < 4 * r := hx
      change dist x p < 32 * R
      linarith
    have hcurvr : -δ ≤ K * r ^ 2 := by
      have hrsq : r ^ 2 ≤ (16 * R) ^ 2 :=
        (sq_le_sq₀ hr.le (by positivity)).mpr (by linarith)
      have hh := mul_le_mul_of_nonneg_left hrsq (abs_nonneg K)
      have hk := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)
      linarith
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
      linarith
    exact haffine q r hr hcurvr u v
      (fun i => ae_restrict_of_ae_restrict_of_subset hsubr (hu.representative i))
      (hu.continuous.mono hsub4) N χ.sobolev hη hN'

  · intro i
    exact (hfirstv i).mono_error μ hX.quadratic hβ.le hβζ
  · intro i
    exact (hmetricS i).mono_error hρζ

/-- Retain the original uniform-degree interface. -/
theorem regular_neighborhood_bilinear_heat_uniform_degree {K : ℝ} (m : ℕ)
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
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    :
    ∃ d : ℕ, 3 ≤ d ∧ ∀ {radiusCap enlargement ζ : ℝ},
    0 < radiusCap → 0 ≤ enlargement → 0 < ζ →
    ∃ R : ℝ, ∃ hR : 0 < R, ∃ _hRcap : R ≤ radiusCap, ∃ lambda : ℝ, ∃ hlambda : 0 < lambda,
    ∃ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
      (v : X → Euclidean (m + 2)) (e : ℝ)
      (M : PositiveBilinearMeasure X (Euclidean (m + 2))) (Ccut : ℝ)
      (χ : GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (3 * R / 8) Ccut)
      (J : ℕ) (A B D H : ℝ),
      R ≤ 1 ∧ 0 < A ∧ 0 < B ∧ 0 < D ∧ 0 < H ∧ 0 < e ∧ e ≤ 1 ∧
      FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p (32 * R) e u v ∧
      ∀ q ∈ ball p (R / 32),
        let Q := dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ q hR hlambda
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
  obtain ⟨d, hd, hconstruct⟩ := regular_neighborhood_bilinear_heat_with_energy m hX ha
    hcompact hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity
    hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  refine ⟨d, hd, ?_⟩
  intro radiusCap enlargement zeta hcap henlargement hzeta
  obtain ⟨R, hR, hRcap, lambda, hlambda, u, v, e, M, Ccut, chi, J, A, B, D, H, _L,
    hR1, hA, hB, hD, hH, he, he1, hu, _hL, _henergy, hlocal⟩ :=
    hconstruct hcap henlargement hzeta
  exact ⟨R, hR, hRcap, lambda, hlambda, u, v, e, M, Ccut, chi, J, A, B, D, H,
    hR1, hA, hB, hD, hH, he, he1, hu, fun q hq => (hlocal q hq).2⟩

/-- The capped interface retains the original argument order. -/
theorem regular_neighborhood_bilinear_heat_with_cap {K : ℝ} (m : ℕ)
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
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    {radiusCap : ℝ} (hRadiusCap : 0 < radiusCap)
    {enlargement ζ : ℝ} (henlargement : 0 ≤ enlargement) (hζ : 0 < ζ) :
    ∃ R : ℝ, ∃ hR : 0 < R, ∃ _hRcap : R ≤ radiusCap, ∃ lambda : ℝ, ∃ hlambda : 0 < lambda,
    ∃ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
      (v : X → Euclidean (m + 2)) (e : ℝ)
      (M : PositiveBilinearMeasure X (Euclidean (m + 2))) (Ccut : ℝ)
      (χ : GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (3 * R / 8) Ccut)
      (J d : ℕ) (A B D H : ℝ),
      R ≤ 1 ∧ 3 ≤ d ∧ 0 < A ∧ 0 < B ∧ 0 < D ∧ 0 < H ∧ 0 < e ∧ e ≤ 1 ∧
      FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p (32 * R) e u v ∧
      ∀ q ∈ ball p (R / 32),
        let Q := dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ q hR hlambda
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
  obtain ⟨d, hd, hconstruct⟩ := regular_neighborhood_bilinear_heat_uniform_degree m hX ha
    hcompact hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity
    hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  obtain ⟨R, hR, hRcap, lambda, hlambda, u, v, e, M, Ccut, chi, J, A, B, D, H,
    hR1, hA, hB, hD, hH, he, he1, hu, hlocal⟩ := hconstruct hRadiusCap henlargement hζ
  exact ⟨R, hR, hRcap, lambda, hlambda, u, v, e, M, Ccut, chi, J, d, A, B, D, H,
    hR1, hd, hA, hB, hD, hH, he, he1, hu, hlocal⟩

/-- The uncapped heat statement follows with unit radius cap. -/
theorem regular_neighborhood_bilinear_heat {K : ℝ} (m : ℕ)
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
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    {enlargement ζ : ℝ} (henlargement : 0 ≤ enlargement) (hζ : 0 < ζ) :
    ∃ R : ℝ, ∃ hR : 0 < R, ∃ lambda : ℝ, ∃ hlambda : 0 < lambda,
    ∃ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
      (v : X → Euclidean (m + 2)) (e : ℝ)
      (M : PositiveBilinearMeasure X (Euclidean (m + 2))) (Ccut : ℝ)
      (χ : GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (3 * R / 8) Ccut)
      (J d : ℕ) (A B D H : ℝ),
      R ≤ 1 ∧ 3 ≤ d ∧ 0 < A ∧ 0 < B ∧ 0 < D ∧ 0 < H ∧ 0 < e ∧ e ≤ 1 ∧
      FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p (32 * R) e u v ∧
      ∀ q ∈ ball p (R / 32),
        let Q := dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ q hR hlambda
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
  obtain ⟨R, hR, _hcap, hrest⟩ := regular_neighborhood_bilinear_heat_with_cap m hX ha
    hcompact hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity
    hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
    (radiusCap := 1) zero_lt_one henlargement hζ
  exact ⟨R, hR, hrest⟩

end RegularPointCoordinates

end

end OAI
