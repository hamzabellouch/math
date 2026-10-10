import OAI.Geometry.RCD.Coordinates.NormalizedRadialError
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates
import OAI.Geometry.RCD.Coordinates.DyadicRadialFits

namespace OAI

/-! # Qualitative radial smallness for the actual dyadic distance datum -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The global extensions of the original harmonic coordinates need not
be bounded: clipping preserves their actual local radial error. -/
theorem local_normalized_radial_error {n : ℕ} {p : X} {r ε Cχ Q : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCχ : 0 ≤ Cχ) (hQb : 0 ≤ Q)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * r) ε u v)
    (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 r 4 ε (fun x => r⁻¹ • v x))
    (q : SobolevSpace μ hQ)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict (ball p (4 * r))] fun x => dist p x ^ 2 / 2)
    (hqbound : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ q x| ≤ Q)
    (heik : ∀ᵐ x ∂μ.restrict (ball p (4 * r)), localGamma μ hQ q q x = 2 * SobolevSpace.toLp μ hQ q x)
    (χ : GoodLaplacianCutoff μ hQ p r Cχ)
    (hvol : 0 < μ.real (ball p (4 * r))) (j : Fin n) :
    (∫ x in ball p r, (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) ≤
      (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1)) * ε * r ^ 2 * μ.real (ball p (4 * r)) := by
  obtain ⟨u', hub, hfirst'⟩ := bounded_normalized_splitting μ hQ hr hε hε1 u v hfirst hv hmetric
  have hrep : SobolevSpace.toLp μ hQ (u' j) =ᵐ[μ.restrict (ball p (4 * r))]
      SobolevSpace.toLp μ hQ (u j) := (hfirst'.representative j).trans (hfirst.representative j).symm
  have hg := localGamma_pair_congr_ae μ hQ (f := q) (f' := q)
    (Filter.Eventually.of_forall fun _ => rfl) hrep
  have hsub : ball p r ⊆ ball p (4 * r) := ball_subset_ball (by linarith)
  have heq : (∫ x in ball p r,
      (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) =
      ∫ x in ball p r, (localGamma μ hQ q (u' j) x - SobolevSpace.toLp μ hQ (u' j) x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hrep,
      ae_restrict_of_ae_restrict_of_subset hsub hg] with x hx hy
    rw [hx, hy]
  rw [heq]
  exact normalized_coordinate_radial_error μ hQ hr hε hε1 hCχ hQb u' v hfirst'
    hv hmetric hub q hq hqbound heik χ hvol j

/-- The same canonical distance datum used for the Poisson corrections
satisfies the local qualitative estimate. Its value and eikonal properties
are derived from the actual source family. -/
theorem DyadicDistanceReplacements.local_radial_error {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    {ε Cχ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCχ : 0 ≤ Cχ)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * (distanceSourceRadius r0 i / 64)) ε u v)
    (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 ε
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • v x))
    (χ : GoodLaplacianCutoff μ hQ p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < μ.real (ball p (4 * (distanceSourceRadius r0 i / 64)))) (j : Fin n) :
    let r := distanceSourceRadius r0 i / 64
    (∫ x in ball p r, (localGamma μ hQ (T.distanceDatum μ hQ i) (u j) x -
      SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) ≤
      (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1)) * ε * r ^ 2 * μ.real (ball p (4 * r)) := by
  dsimp only
  let s := distanceSourceRadius r0 i
  let r := s / 64
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hr : 0 < r := by dsimp only [r]; positivity
  let q := T.distanceDatum μ hQ i
  have hsub : ball p (4 * r) ⊆ ball p (4 * s) := ball_subset_ball (by dsimp only [r]; linarith)
  have hR : 0 ≤ 4 * s := by positivity
  have hrep : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict (ball p (4 * r))]
      fun x => dist p x ^ 2 / 2 := by
    filter_upwards [ae_restrict_of_ae (positiveSquaredDistance_representative μ hQ hR (T.cutoff i)),
      ae_restrict_mem measurableSet_ball] with x hx hxb
    exact hx.trans (positiveSquaredDistanceValue_on_ball μ hQ (T.cutoff i) (hsub hxb))
  have hqb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ q x| ≤ (4 * s) ^ 2 / 2 := by
    filter_upwards [positiveSquaredDistance_representative μ hQ hR (T.cutoff i)] with x hx
    rw [show SobolevSpace.toLp μ hQ q x = positiveSquaredDistanceValue μ hQ (T.cutoff i) x from hx]
    have hb := positiveSquaredDistanceValue_bounds μ hQ hR (T.cutoff i) x
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have heik : ∀ᵐ x ∂μ.restrict (ball p (4 * r)),
      localGamma μ hQ q q x = 2 * SobolevSpace.toLp μ hQ q x := by
    have he := positiveSquaredDistance_energy_value μ hQ hR (T.cutoff i) (S.eikonal i)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub he] with x hx
    change (1 / 2 : ℝ) * localGamma μ hQ q q x = SobolevSpace.toLp μ hQ q x at hx
    linarith
  exact local_normalized_radial_error μ hQ hr hε hε1 hCχ (by positivity)
    u v hfirst hv hmetric q hrep hqb heik χ hvol j

end RegularPointCoordinates

end

end OAI
