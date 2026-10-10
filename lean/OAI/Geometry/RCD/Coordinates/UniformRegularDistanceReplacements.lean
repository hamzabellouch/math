import OAI.Geometry.RCD.Coordinates.RegularDistanceReplacements

namespace OAI

/-! # Poisson replacement constants independent of the error budget -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A regular neighborhood has actual squared-distance replacements with
one set of constants, while the total full source mass is arbitrarily small.
The constants precede the center and every smaller dyadic root. -/
theorem regular_distance_replacements_uniform {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) {p : X} {a κ : ℝ}
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hdistance : LocalSquaredDistanceInput hX)
    (hsobolev : LocalDirichletSobolevInput hX) (hcutoff : LocalGoodCutoffInput hX) :
    letI : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ B J C : ℝ, 0 < B ∧ 0 < J ∧ 1 ≤ C ∧
      ∀ rho eta : ℝ, 0 < rho → 0 < eta → ∃ D : ℝ, 0 < D ∧ D ≤ rho ∧
      ∀ q : X, dist p q ≤ D → ∀ r0 : ℝ, 0 < r0 → r0 ≤ D →
      ∃ S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ q r0,
        Nonempty (DyadicDistanceReplacements (hausdorff (m + 2) X) hX.quadratic S B J C) ∧
        Summable (normalizedDistanceSourceMass (hausdorff (m + 2) X) hX.quadratic S) ∧
        (∑' i, normalizedDistanceSourceMass (hausdorff (m + 2) X) hX.quadratic S i) < eta := by
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨B, J, C, hB, hJ, hC, hreplace⟩ := dyadic_distance_replacements_of_published
    hX (by omega) hsobolev hcutoff hκ
  refine ⟨B, J, C, hB, hJ, hC, ?_⟩
  intro rho eta hrho heta
  obtain ⟨D₁, hD₁, hD₁rho, hsource⟩ := regular_small_distance_sources m hX
    ha hκ hK hrho heta hcompact hregular hvolume hBG hdensity hdistance
  let cap := min rho (min 1 (1 / (64 * (|K| + 1))))
  have hcap : 0 < cap := lt_min hrho (lt_min zero_lt_one (by positivity))
  obtain ⟨D₂, hD₂, hD₂cap, hvol⟩ := exists_uniform_volume_neighborhood (m + 1) ha
    (euclideanUnitVolume_pos (m + 2)) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) hcap hcompact hregular hvolume hBG hdensity
    (fun q r => ne_of_lt (hX.finiteOnBounded (ball q r) isBounded_ball))
  let D := min D₁ D₂
  have hD : 0 < D := lt_min hD₁ hD₂
  refine ⟨D, hD, (min_le_left _ _).trans hD₁rho, ?_⟩
  intro q hq r0 hr0 hrD
  have hq₁ : dist p q ≤ D₁ := hq.trans (min_le_left _ _)
  have hq₂ : dist p q ≤ D₂ := hq.trans (min_le_right _ _)
  have hrD₁ : r0 ≤ D₁ := hrD.trans (min_le_left _ _)
  have hrD₂ : r0 ≤ D₂ := hrD.trans (min_le_right _ _)
  obtain ⟨S, hsum, hsmall⟩ := hsource q hq₁ r0 hr0 hrD₁
  have hrone : r0 ≤ 1 := hrD₂.trans (hD₂cap.trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hrcap : r0 ≤ 1 / (64 * (|K| + 1)) := hrD₂.trans (hD₂cap.trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hradii (i : ℕ) : distanceSourceRadius r0 i ≤ r0 := by
    have hh := distanceSourceRadius_outer_le hr0.le i
    have hp := distanceSourceRadius_pos hr0 i
    linarith
  have hcurv (i : ℕ) : -1 ≤ K * (64 * distanceSourceRadius r0 i) ^ 2 :=
    curvature_bound_sixtyfour (distanceSourceRadius_pos hr0 i).le ((hradii i).trans hrcap)
  have hann (i : ℕ) :
      0 < (hausdorff (m + 2) X).real (ball q (distanceSourceRadius r0 i)) ∧
      2 * (hausdorff (m + 2) X).real (ball q (distanceSourceRadius r0 i)) ≤
        (hausdorff (m + 2) X).real (ball q (2 * distanceSourceRadius r0 i)) := by
    apply relative_volume_annulus (n := m + 2) (by omega) (distanceSourceRadius_pos hr0 i)
      (euclideanUnitVolume_pos (m + 2))
    · exact hvol q hq₂ _ (distanceSourceRadius_pos hr0 i) ((hradii i).trans hrD₂)
    · exact hvol q hq₂ _ (mul_pos (by norm_num) (distanceSourceRadius_pos hr0 i))
        ((distanceSourceRadius_outer_le hr0.le i).trans hrD₂)
  exact ⟨S, hreplace q r0 S hrone hcurv (fun i => (hann i).1) (fun i => (hann i).2), hsum, hsmall⟩

end RegularPointCoordinates

end

end OAI
