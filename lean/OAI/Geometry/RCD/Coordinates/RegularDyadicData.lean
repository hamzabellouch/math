import OAI.Geometry.RCD.Coordinates.DyadicNormalizedFamily
import OAI.Geometry.RCD.Coordinates.InitialAnalyticBounds
import OAI.Geometry.RCD.Heat.HeatRegimeBridges
import OAI.Geometry.RCD.Coordinates.ScaledCoordinates
import OAI.Geometry.RCD.Coordinates.MetricDyadicNormalization

namespace OAI

/-! # One regular-point map with bounded dyadic frames and one Bochner measure -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published geometric normalization and local Bochner inputs provide
the actual common data required by the heat argument. The root frames are
bounded before any small-scale heat comparison is invoked. -/
theorem regular_uniform_dyadic_data_with_cap {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) (hn : 2 ≤ m + 1) {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 1) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 1) X) (m + 1) p
      (euclideanUnitVolume (m + 1)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 1) X) (m + 1) p)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 1) X)
      (comparisonModelVolume m a) y (euclideanUnitVolume (m + 1)))
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX)
    {radiusCap : ℝ} (hRadiusCap : 0 < radiusCap)
    {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ R ε : ℝ, 0 < R ∧ R ≤ radiusCap ∧ 16 * R < 1 ∧ a * (48 * R) ≤ 1 ∧
      |K| * (16 * R) ^ 2 ≤ β ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∃ (L : ℝ≥0) (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
        (v : X → Euclidean (m + 1)) (M : PositiveBilinearMeasure X (Euclidean (m + 1))),
        (L : ℝ) ^ 2 ≤ 4 * ((m + 1 : ℕ) : ℝ) ^ 2 ∧
        FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (32 * R) ε u v ∧
        (∀ z, Nonempty (LocalHarmonicEnergy (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) M |K| p (4 * R)
          L z)) ∧
        (∀ y, dist p y ≤ 16 * R → ∀ r, 0 < r → r ≤ 32 * R →
          |(hausdorff (m + 1) X).real (ball y r) /
            (euclideanUnitVolume (m + 1) * r ^ (m + 1)) - 1| ≤ 1 / 2) ∧
        (∀ q ∈ ball p R,
          ∃ S : ℕ → Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1),
            (∀ i, IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
              (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
              (ball q (R / 2 ^ i)) measurableSet_ball (S i)) ∧
            (∀ i, ∃ w : X → Euclidean (m + 1),
              FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic q (R / 2 ^ i) β
                (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i)) w) ∧
            ‖(S 0 : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))‖ ^ 2 ≤ 2 ∧
            (∀ i, FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic q (R / 2 ^ i) β
              (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i))
              (fun x => (S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x))) ∧
            ∀ i, IsPointedApproximation q 0 ((R / 2 ^ i) / 128) 4 (8 * ρ)
              (fun x => ((R / 2 ^ i) / 128)⁻¹ •
                ((S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x) -
                  (S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v q)))) ∧
        ∀ q ∈ ball p R, ∀ r : ℝ, 0 < r → r ≤ R / 16 →
          ∃ B : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1),
            IsPointedApproximation q 0 r 2 (4 * ρ) (fun x =>
              (B : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x) -
              (B : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v q)) := by
  let μ := hausdorff (m + 1) X
  let C := 3 * (32 : ℝ) ^ (m + 1)
  have hC : 1 ≤ C := by
    have hpow : (1 : ℝ) ≤ 32 ^ (m + 1) := one_le_pow₀ (by norm_num)
    dsimp only [C]
    linarith
  let cap := min 1 (1 / (2 * (((m + 1 : ℕ) : ℝ) ^ 2 * C + 1)))
  have hcap : 0 < cap := lt_min zero_lt_one (by dsimp only [C]; positivity)
  have homega := euclideanUnitVolume_pos (m + 1)
  obtain ⟨D, hD, _, hvolD⟩ := exists_uniform_volume_neighborhood (μ := μ) m ha homega
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) zero_lt_one
    hcompact hregular hvolume hBG hdensity
    (fun y r => ne_of_lt (hX.finiteOnBounded (ball y r) isBounded_ball))
  obtain ⟨T, ε, hT, hε, hTcap, hεcap, hT1, hscale, hcurv, u, v, hu, hfamily⟩ :=
    bounded_regular_controlled_normalization m hX hn ha hcompact hregular hvolume hmeasured hBG
      hdensity hinitial htrans hsplit hrigidity hρ hβ
      (Rcap := min (D / 4) radiusCap) (lt_min (by positivity) hRadiusCap) hcap
  have hTD : T ≤ D / 4 := hTcap.trans (min_le_left _ _)
  let R := T / 16
  have hR : 0 < R := div_pos hT (by norm_num)
  have hTR : 16 * R = T := by dsimp only [R]; ring
  have h32R : 32 * R = 2 * T := by dsimp only [R]; ring
  have hε1 : ε ≤ 1 := hεcap.trans (min_le_left _ _)
  have hεsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (C * ε) ≤ 1 / 2 := by
    have he := hεcap.trans (min_le_right _ _)
    have hden : 0 < 2 * (((m + 1 : ℕ) : ℝ) ^ 2 * C + 1) := by dsimp only [C]; positivity
    have hm := (le_div_iff₀ hden).mp he
    nlinarith only [hm, hε.le]
  have hu' : FirstOrderSplittingOn μ hX.quadratic p (8 * (T / 4)) ε u v := by
    simpa only [show 8 * (T / 4) = 2 * T by ring] using hu
  obtain ⟨M, hM⟩ := hu'.local_bochner hX hbochner (abs_nonneg K) (neg_abs_le K)
    (by positivity) hε.le
  have hvol : ∀ y, dist p y ≤ 16 * R → ∀ r, 0 < r → r ≤ 32 * R →
      |μ.real (ball y r) / (euclideanUnitVolume (m + 1) * r ^ (m + 1)) - 1| ≤ 1 / 2 := by
    intro y hy r hr hrR
    apply hvolD y (by rw [hTR] at hy; linarith) r hr
    rw [h32R] at hrR
    linarith
  refine ⟨R, ε, hR, by
    have hh := hTcap.trans (min_le_right _ _)
    dsimp only [R]
    linarith, by rwa [hTR], ?_, by rwa [hTR], hε, hε1,
    splittingDirectionBound (m + 1) ε hε.le, u, v, M,
    splittingDirectionBound_sq_le hε.le hε1, by simpa only [h32R] using hu, ?_, hvol, ?_, ?_⟩
  · have he : 48 * R = 3 * T := by dsimp only [R]; ring
    rwa [he]
  · have he : 4 * R = T / 4 := by dsimp only [R]; ring
    simpa only [he] using hM
  · intro q hq
    have hqp : dist q p < R := hq
    have hqT : q ∈ ball p (T / 4) := by
      change dist q p < T / 4
      dsimp only [R] at hqp
      linarith
    obtain ⟨S, hS, hfirst, hmetricS⟩ := exists_metric_dyadic_normalized_family μ hX.quadratic u v q hR
      (show 4 * R ≤ T by dsimp only [R]; linarith) (hfamily q hqT)
    refine ⟨S, hS, fun i => ⟨_, hfirst i⟩, ?_, hfirst, hmetricS⟩
    have hsub : ball q R ⊆ ball p (2 * T) := by
      intro x hx
      have hxq : dist x q < R := hx
      have hxp := dist_triangle x q p
      change dist x p < 2 * T
      dsimp only [R] at hxq hqp
      linarith
    have hratio : μ.real (ball p (2 * T)) ≤ C * μ.real (ball q R) := by
      apply initial_working_volume_ratio μ (m + 1) p q hT homega
      · apply hvol p (by simp only [dist_self]; positivity) (2 * T) (by positivity)
        rw [h32R]
      · apply hvol q (by rw [dist_comm]; linarith) R hR
        linarith
    apply initial_normalizer_norm_sq_le_two μ hX.quadratic u hu (ball q R) measurableSet_ball hsub
      (ne_of_gt (hX.fullSupport q R hR)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (ne_of_gt (hX.fullSupport p (2 * T) (by positivity)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hC hε.le hratio hεsmall (S 0)
    simpa only [pow_zero, div_one] using hS 0

  · intro q hq r hr hrR
    have hqp : dist q p < R := hq
    have hqT : q ∈ ball p (T / 4) := by
      change dist q p < T / 4
      dsimp only [R] at hqp
      linarith
    have hrT : 64 * (4 * r) ≤ T := by
      dsimp only [R] at hrR
      linarith
    obtain ⟨A, _, _, happ⟩ := hfamily q hqT (4 * r) (by positivity) hrT
    exact ⟨scaledCoordinateEquiv A r⁻¹ (inv_ne_zero hr.ne'),
      normalized_approximation_rescale_four hr v A happ⟩

/-- The original uncapped interface is the unit-cap specialization. -/
theorem regular_uniform_dyadic_data {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) (hn : 2 ≤ m + 1) {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 1) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 1) X) (m + 1) p
      (euclideanUnitVolume (m + 1)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 1) X) (m + 1) p)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 1) X)
      (comparisonModelVolume m a) y (euclideanUnitVolume (m + 1)))
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX)
    {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ R ε : ℝ, 0 < R ∧ 16 * R < 1 ∧ a * (48 * R) ≤ 1 ∧
      |K| * (16 * R) ^ 2 ≤ β ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∃ (L : ℝ≥0) (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
        (v : X → Euclidean (m + 1)) (M : PositiveBilinearMeasure X (Euclidean (m + 1))),
        (L : ℝ) ^ 2 ≤ 4 * ((m + 1 : ℕ) : ℝ) ^ 2 ∧
        FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (32 * R) ε u v ∧
        (∀ z, Nonempty (LocalHarmonicEnergy (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) M |K| p (4 * R)
          L z)) ∧
        (∀ y, dist p y ≤ 16 * R → ∀ r, 0 < r → r ≤ 32 * R →
          |(hausdorff (m + 1) X).real (ball y r) /
            (euclideanUnitVolume (m + 1) * r ^ (m + 1)) - 1| ≤ 1 / 2) ∧
        (∀ q ∈ ball p R,
          ∃ S : ℕ → Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1),
            (∀ i, IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
              (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
              (ball q (R / 2 ^ i)) measurableSet_ball (S i)) ∧
            (∀ i, ∃ w : X → Euclidean (m + 1),
              FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic q (R / 2 ^ i) β
                (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i)) w) ∧
            ‖(S 0 : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))‖ ^ 2 ≤ 2 ∧
            (∀ i, FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic q (R / 2 ^ i) β
              (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i))
              (fun x => (S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x))) ∧
            ∀ i, IsPointedApproximation q 0 ((R / 2 ^ i) / 128) 4 (8 * ρ)
              (fun x => ((R / 2 ^ i) / 128)⁻¹ •
                ((S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x) -
                  (S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v q)))) ∧
        ∀ q ∈ ball p R, ∀ r : ℝ, 0 < r → r ≤ R / 16 →
          ∃ B : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1),
            IsPointedApproximation q 0 r 2 (4 * ρ) (fun x =>
              (B : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x) -
              (B : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v q)) := by
  obtain ⟨R, epsilon, hR, _hcap, hrest⟩ := regular_uniform_dyadic_data_with_cap m hX hn ha
    hcompact hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity hbochner
    (radiusCap := 1) zero_lt_one hρ hβ
  exact ⟨R, epsilon, hR, hrest⟩

end RegularPointCoordinates

end

end OAI
