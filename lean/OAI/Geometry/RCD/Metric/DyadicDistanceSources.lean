import OAI.Geometry.RCD.Metric.DistanceSourceMeasure

namespace OAI

/-! # A fixed dyadic family of actual squared-distance sources -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

def distanceSourceRadius (r0 : ℝ) (i : ℕ) : ℝ := r0 / (2 : ℝ) ^ (i + 1)

theorem distanceSourceRadius_pos {r0 : ℝ} (hr0 : 0 < r0) (i : ℕ) :
    0 < distanceSourceRadius r0 i := by unfold distanceSourceRadius; positivity

theorem distanceSourceRadius_succ (r0 : ℝ) (i : ℕ) :
    distanceSourceRadius r0 (i + 1) = distanceSourceRadius r0 i / 2 := by
  simp only [distanceSourceRadius, pow_succ]
  ring

theorem distanceSourceRadius_outer_le {r0 : ℝ} (hr0 : 0 ≤ r0) (i : ℕ) :
    2 * distanceSourceRadius r0 i ≤ r0 := by
  have hp : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hdiv : r0 / 2 ^ i ≤ r0 := div_le_self hr0 hp
  calc
    _ = r0 / 2 ^ i := by unfold distanceSourceRadius; rw [pow_succ]; ring
    _ ≤ r0 := hdiv

theorem distanceSourceRadius_four_sq (r0 : ℝ) (i : ℕ) :
    (4 * distanceSourceRadius r0 i) ^ 2 = 4 * r0 ^ 2 * (1 / 4 : ℝ) ^ i := by
  induction i with
  | zero => simp only [distanceSourceRadius, pow_zero, mul_one]; ring
  | succ i ih =>
    rw [distanceSourceRadius_succ, show (4 * (distanceSourceRadius r0 i / 2)) ^ 2 =
      (4 * distanceSourceRadius r0 i) ^ 2 / 4 by ring, ih, pow_succ]
    ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Each source is the genuine positive Laplacian defect on four times
its testing radius. The same scalar source value is used at all centers. -/
structure DyadicDistanceSources (n : ℕ) (κ : ℝ) (p : X) (r0 : ℝ) where
  radius_pos : 0 < r0
  source : ℕ → Measure X
  finite : ∀ i, IsFiniteMeasure (source i)
  eikonal : ∀ i, ∀ᵐ x ∂μ.restrict (ball p (4 * distanceSourceRadius r0 i)),
    localGamma μ hQ (inwardSobolev μ hQ p (4 * distanceSourceRadius r0 i))
      (inwardSobolev μ hQ p (4 * distanceSourceRadius r0 i)) x = 1
  defect : ∀ i, ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
    LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p (4 * distanceSourceRadius r0 i) →
    SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
    energyForm μ hQ (inwardQuadratic μ hQ p
      (by have := distanceSourceRadius_pos radius_pos i; positivity : 0 ≤ 4 * distanceSourceRadius r0 i)) ψ +
      ((n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2) * (∫ x, v x ∂μ) = ∫ x, v x ∂source i

theorem dyadic_distance_sources_of_published {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hdistance : LocalSquaredDistanceInput hX)
    {κ r0 : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K) (p : X) (hr0 : 0 < r0) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    Nonempty (DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0) := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  have hex (i : ℕ) := hdistance hn κ hκ hK p (4 * distanceSourceRadius r0 i)
    (by have := distanceSourceRadius_pos hr0 i; positivity)
  choose σ hfinite heik hdefect using hex
  exact ⟨⟨hr0, σ, hfinite, heik, hdefect⟩⟩

theorem DyadicDistanceSources.mass_le {n : ℕ} {κ r0 : ℝ} {p : X}
    (D : DyadicDistanceSources μ hQ n κ p r0) (hn : 0 < n) (hκ : 0 ≤ κ)
    {model : ℝ → ℝ} (hBG : BallVolumeComparison μ model) (hmodel : Continuous model)
    (hmodelpos : ∀ r, 0 < r → 0 < model r) (i : ℕ) :
    let r := distanceSourceRadius r0 i
    ((r ^ (-(n : ℝ)) - (2 * r) ^ (-(n : ℝ))) / n) * (D.source i).real (ball p r) ≤
      r ^ (-(n : ℝ)) * μ.real (ball p r) - (2 * r) ^ (-(n : ℝ)) * μ.real (ball p (2 * r)) +
        (κ * (4 * r) ^ 2) * ((r ^ (-(n : ℝ)) - (2 * r) ^ (-(n : ℝ))) / n) * μ.real (ball p (2 * r)) := by
  let _ := D.finite i
  have hr := distanceSourceRadius_pos D.radius_pos i
  have heik := inwardSobolev_eikonal_mono μ hQ p
    (by linarith : 2 * distanceSourceRadius r0 i ≤ 4 * distanceSourceRadius r0 i) (D.eikonal i)
  exact squaredDistance_source_mass_le μ hQ (by exact_mod_cast hn) hr (by linarith)
    (by linarith) (by positivity) p (D.source i) hBG hmodel (hmodelpos _ hr)
    ((ae_restrict_iff' measurableSet_ball).mp heik) (D.defect i)

end RegularPointCoordinates

end

end OAI
