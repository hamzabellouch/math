import OAI.Geometry.RCD.Coordinates.RegularControlledNormalization

namespace OAI

/-! # Choosing the normalization radius and raw error under prescribed caps -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published normalization inputs allow the working radius and the
raw initial error to be capped independently of the later target error. -/
theorem bounded_regular_controlled_normalization {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) (hn : 2 ≤ m + 1) {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 1) p)
    (_hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 1) X) (m + 1) p
      (euclideanUnitVolume (m + 1)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 1) X) (m + 1) p)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (_hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 1) X)
      (comparisonModelVolume m a) y (euclideanUnitVolume (m + 1)))
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    {Rcap εcap : ℝ} (hRcap : 0 < Rcap) (hεcap : 0 < εcap) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧ R ≤ Rcap ∧ ε ≤ εcap ∧ R < 1 ∧ a * (3 * R) ≤ 1 ∧ |K| * R ^ 2 ≤ β ∧
      ∃ (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
        (v : X → Euclidean (m + 1)),
        FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 * R) ε u v ∧
        ∀ q ∈ ball p (R / 4), ∀ r : ℝ, 0 < r → 64 * r ≤ R →
          ∃ A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1),
            IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
              (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
              (ball q (16 * r)) measurableSet_ball A ∧
            FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic q (16 * r) β
              (transformedColumn (hausdorff (m + 1) X) hX.quadratic u A)
              (fun x => (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x)) ∧
            IsPointedApproximation q 0 r (1 / 2) ρ
              (fun x => r⁻¹ • ((A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x) -
                (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v q))) := by
  obtain ⟨δ, hδ, hnormalize⟩ := uniform_controlled_coordinates_of_comparison m hX hn
    htrans hsplit ha hBG hρ hβ
  obtain ⟨D, hD, hflat⟩ := hrigidity p hregular δ hδ
  let ε := min δ εcap
  have hε : 0 < ε := lt_min hδ hεcap
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεεcap : ε ≤ εcap := min_le_right _ _
  obtain ⟨T, hT, hinitialize⟩ := regular_initial_splitting_at_all_small_scales hX hn
    hcompact hregular hmeasured hinitial hε
  have hcap : 0 < min (β / (|K| + 1))
      (min D (min T (min 1 (min (ε / (|K| + 1)) (1 / (3 * (a + 1))))))) :=
    lt_min (by positivity)
      (lt_min hD (lt_min hT (lt_min zero_lt_one (lt_min (by positivity) (by positivity)))))
  obtain ⟨R, hR, hRboth⟩ := exists_between (lt_min hRcap hcap)
  rcases lt_min_iff.mp hRboth with ⟨hRcap', hRbound⟩
  rcases lt_min_iff.mp hRbound with ⟨hRβ, hRbound⟩
  rcases lt_min_iff.mp hRbound with ⟨hRD, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hRT, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hR1, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hRK, hRa⟩
  obtain ⟨u, v, hu⟩ := hinitialize R hR hRT
  have hcurv : -ε ≤ K * R ^ 2 := by
    have he : R * (|K| + 1) ≤ ε := (le_div_iff₀ (by positivity)).mp hRK.le
    have hs : R ^ 2 ≤ R := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg K)
    have hK := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg R)
    nlinarith
  have hscale : a * (3 * R) ≤ 1 := by
    have he := (lt_div_iff₀ (by positivity : 0 < 3 * (a + 1))).mp hRa
    nlinarith
  have hcurvβ : |K| * R ^ 2 ≤ β := by
    have hb := (lt_div_iff₀ (by positivity : 0 < |K| + 1)).mp hRβ
    have hs : R ^ 2 ≤ R := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg K)
    nlinarith
  refine ⟨R, ε, hR, hε, hRcap'.le, hεεcap, hR1, hscale, hcurvβ, u, v, hu, ?_⟩
  apply hnormalize p R hR (by linarith) hscale u v
    (hu.mono_error (hausdorff (m + 1) X) hX.quadratic hε.le hεδ)
  intro q hq s hs hsR
  apply hflat q ?_ s hs (by linarith)
  have hh := mem_ball.mp hq
  rw [dist_comm] at hh
  linarith

end RegularPointCoordinates

end

end OAI
