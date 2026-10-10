import OAI.Geometry.RCD.Coordinates.UniformRegularDistanceReplacements
import OAI.Geometry.RCD.Sobolev.PoissonDefectBudget

namespace OAI

/-! # A fixed Poisson family for arbitrarily small regular-neighborhood defects -/

open Set Metric MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual replacements, their full source-plus-curvature budget and
the volume annulus needed for radial correction all hold in one neighborhood.
The constants precede the center and every smaller root radius. -/
theorem regular_poisson_defect_uniform {K : ℝ} (m : ℕ)
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
        Summable (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S) ∧
        (∑' i, normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S i) < eta ∧
        ∀ r : ℝ, 0 < r → r ≤ r0 →
          |(hausdorff (m + 2) X).real (ball q r) /
            (euclideanUnitVolume (m + 2) * r ^ (m + 2)) - 1| ≤ 1 / 4 := by
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨B, J, C, hB, hJ, hC, hreplacements⟩ :=
    regular_distance_replacements_uniform m hX ha hκ hK hcompact hregular hvolume hBG
      hdensity hdistance hsobolev hcutoff
  refine ⟨B, J, C, hB, hJ, hC, ?_⟩
  intro rho eta hrho heta
  let omega := euclideanUnitVolume (m + 2)
  have homega : 0 < omega := euclideanUnitVolume_pos _
  let F := κ * (2 * omega) / 3
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  let cap := min rho (Real.sqrt (eta / (4 * (F + 1))))
  have hcap : 0 < cap := lt_min hrho (Real.sqrt_pos.mpr (by positivity))
  obtain ⟨D₁, hD₁, hD₁cap, hdata⟩ := hreplacements cap (eta / 2) hcap (half_pos heta)
  obtain ⟨D₂, hD₂, hD₂cap, hvol⟩ := exists_uniform_volume_neighborhood (m + 1) ha
    homega (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    hcap hcompact hregular hvolume hBG hdensity
    (fun q r => ne_of_lt (hX.finiteOnBounded (ball q r) isBounded_ball))
  let D := min D₁ D₂
  have hD : 0 < D := lt_min hD₁ hD₂
  refine ⟨D, hD, (min_le_left _ _).trans (hD₁cap.trans (min_le_left _ _)), ?_⟩
  intro q hq r0 hr0 hrD
  obtain ⟨S, hT, hsum, hsmall⟩ := hdata q (hq.trans (min_le_left _ _)) r0 hr0
    (hrD.trans (min_le_left _ _))
  have hlocal (r : ℝ) (hr : 0 < r) (hrr : r ≤ r0) :
      |(hausdorff (m + 2) X).real (ball q r) / (omega * r ^ (m + 2)) - 1| ≤ 1 / 4 :=
    hvol q (hq.trans (min_le_right _ _)) r hr
      (hrr.trans (hrD.trans (min_le_right _ _)))
  have hnormalized (i : ℕ) :
      (distanceSourceRadius r0 i) ^ (-((m + 2 : ℕ) : ℝ)) *
        (hausdorff (m + 2) X).real (ball q (distanceSourceRadius r0 i)) ≤ 2 * omega := by
    have hs := distanceSourceRadius_pos hr0 i
    have hsle : distanceSourceRadius r0 i ≤ r0 := by
      have hh := distanceSourceRadius_outer_le hr0.le i
      linarith
    have hv := (normalized_volume_bounds hs homega (hlocal _ hs hsle)).2
    linarith
  obtain ⟨hPsum, hPbound⟩ := S.poisson_defect_budget (hausdorff (m + 2) X)
    hX.quadratic hκ (by positivity : 0 ≤ 2 * omega) hsum hnormalized
  have hroot : r0 ≤ Real.sqrt (eta / (4 * (F + 1))) :=
    hrD.trans ((min_le_left _ _).trans (hD₁cap.trans (min_le_right _ _)))
  have hrootsq : r0 ^ 2 ≤ eta / (4 * (F + 1)) := by
    have hh := (sq_le_sq₀ hr0.le (Real.sqrt_nonneg _)).mpr hroot
    rwa [Real.sq_sqrt (by positivity : 0 ≤ eta / (4 * (F + 1)))] at hh
  have hcurv : κ * (2 * omega) * r0 ^ 2 / 3 ≤ eta / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (F + 1))).mp hrootsq
    rw [show κ * (2 * omega) * r0 ^ 2 / 3 = F * r0 ^ 2 by dsimp only [F]; ring]
    nlinarith [sq_nonneg r0]
  exact ⟨S, hT, hPsum, by linarith, hlocal⟩

end RegularPointCoordinates

end

end OAI
