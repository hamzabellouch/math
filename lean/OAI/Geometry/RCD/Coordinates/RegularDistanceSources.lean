import OAI.Geometry.RCD.Metric.AlmostEuclideanSourceBudget
import OAI.Geometry.RCD.Metric.VolumeRegime
import OAI.Geometry.RCD.Metric.VolumeRigidityInput

namespace OAI

/-! # Uniformly small full distance sources near a regular point -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The same neighborhood works for every center and every smaller root
radius. Both the full source and its small total mass are constructed. -/
theorem regular_small_distance_sources {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) {p : X} {a κ rho eta : ℝ}
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hrho : 0 < rho) (heta : 0 < eta)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hdistance : LocalSquaredDistanceInput hX) :
    letI : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ D : ℝ, 0 < D ∧ D ≤ rho ∧ ∀ q : X, dist p q ≤ D →
      ∀ r0 : ℝ, 0 < r0 → r0 ≤ D →
      ∃ S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ q r0,
        Summable (normalizedDistanceSourceMass (hausdorff (m + 2) X) hX.quadratic S) ∧
        (∑' i, normalizedDistanceSourceMass (hausdorff (m + 2) X) hX.quadratic S i) < eta := by
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let omega := euclideanUnitVolume (m + 2)
  have homega : 0 < omega := euclideanUnitVolume_pos _
  let A := 2 * (radialCutoffCoefficient ((m + 2 : ℕ) : ℝ))⁻¹ * omega
  have hA : 0 ≤ A := by
    have := (radialCutoffCoefficient_pos (n := ((m + 2 : ℕ) : ℝ)) (by positivity)).le
    dsimp only [A]
    positivity
  let C := (16 / 3 : ℝ) * κ * omega * (2 : ℝ) ^ ((m + 2 : ℕ) : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let B := 1 + 2 * C
  have hB : 0 < B := by dsimp only [B]; linarith
  let eps := min (1 / 2 : ℝ) (eta / (4 * (A + 1)))
  have heps : 0 < eps := lt_min (by norm_num) (by positivity)
  have heps1 : eps ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hfirst : A * eps ≤ eta / 4 := by
    have hepsle : eps ≤ eta / (4 * (A + 1)) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (A + 1))).mp hepsle
    nlinarith
  let cap := min rho (Real.sqrt (eta / (4 * B)))
  have hcap : 0 < cap := lt_min hrho (Real.sqrt_pos.mpr (by positivity))
  obtain ⟨D, hD, hDcap, hvol⟩ := exists_uniform_volume_neighborhood (m + 1) ha homega heps heps1
    hcap hcompact hregular hvolume hBG hdensity
    (fun q r => ne_of_lt (hX.finiteOnBounded (ball q r) isBounded_ball))
  refine ⟨D, hD, hDcap.trans (min_le_left _ _), ?_⟩
  intro q hq r0 hr0 hrD
  obtain ⟨S⟩ := dyadic_distance_sources_of_published hX (by omega) hdistance hκ hK q hr0
  have hlocal : ∀ r, 0 < r → r ≤ r0 →
      |(hausdorff (m + 2) X).real (ball q r) / (omega * r ^ (m + 2)) - 1| ≤ eps :=
    fun r hr hrr => hvol q hq r hr (hrr.trans hrD)
  obtain ⟨hs, hb⟩ := S.almost_euclidean_budget (hausdorff (m + 2) X) hX.quadratic
    (by omega) hκ homega heps.le hBG (continuous_comparisonModelVolume _ _)
    (fun r hr => comparisonModelVolume_pos _ ha hr) hlocal
  refine ⟨S, hs, ?_⟩
  have hrsmall : r0 ≤ Real.sqrt (eta / (4 * B)) :=
    hrD.trans (hDcap.trans (min_le_right _ _))
  have hrsq : r0 ^ 2 ≤ eta / (4 * B) := by
    have hh := (sq_le_sq₀ hr0.le (Real.sqrt_nonneg _)).mpr hrsmall
    rwa [Real.sq_sqrt (by positivity : 0 ≤ eta / (4 * B))] at hh
  have hsmall : B * r0 ^ 2 ≤ eta / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp hrsq
    nlinarith
  have hcoef : C * (1 + eps) ≤ B := by dsimp only [B]; nlinarith
  have hcurv : (4 * κ * r0 ^ 2 * ((1 + eps) * omega) *
      (2 : ℝ) ^ ((m + 2 : ℕ) : ℝ)) * (4 / 3) ≤ B * r0 ^ 2 := by
    calc
      _ = C * (1 + eps) * r0 ^ 2 := by dsimp only [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  have hmain : 2 * (radialCutoffCoefficient ((m + 2 : ℕ) : ℝ))⁻¹ * eps * omega = A * eps := by
    dsimp only [A]
    ring
  rw [hmain] at hb
  linarith

end RegularPointCoordinates

end

end OAI
