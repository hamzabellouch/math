import OAI.Geometry.RCD.Coordinates.RegularCenterRadialData
import OAI.Geometry.RCD.Sobolev.ActualPoissonDifference
import OAI.Geometry.RCD.Sobolev.PoissonPairSpan
import OAI.Geometry.RCD.Sobolev.PoissonSpanLift
import OAI.Geometry.RCD.Sobolev.BochnerMassComparison
import OAI.Geometry.RCD.Transport.LocalBochnerTransport

namespace OAI

/-! # The common Bochner span of the constructed Poisson pair -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual pair has a single full Bochner measure. Its difference mass
is bounded by the source defects, and its coordinate block controls the
original heat measure on the smaller ball. All objects come from the cited
local calculus and cutoff inputs. -/
theorem regular_pair_bochner {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hhessian : LocalPoissonHessianInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hn : 2 ≤ n) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ {base first center : X} {a B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker},
    0 ≤ A → 0 ≤ Cχ →
    ∀ (e : RegularProjectionEnvironment hX base hk a |K| B J C A Cχ enlargement zeta eta),
    center ∈ ball base (e.heat.radius / 32) →
    ∀ (d1 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca first)
      (d2 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca center) (i : ℕ),
    let s := distanceSourceRadius e.heat.radius i
    let f : Fin 2 → SobolevSpace (hausdorff n X) hX.quadratic :=
      ![d1.replacement.replacement i, d2.replacement.replacement i]
    let U := sobolevColumnMap (hausdorff n X) hX.quadratic
      (poissonSpan (hausdorff n X) hX.quadratic e.heat.coordinates f)
    let v1 : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (0 : Fin 2)) 1
    let v2 : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (1 : Fin 2)) 1
    dist center first ≤ s / 4 →
    ∃ (L : ℝ≥0) (M : PositiveBilinearMeasure X (Euclidean (n + 2))),
      (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic
        U M |K| center (s / 32) L v)) ∧
      ⟪v2 - v1, M.massOperator (ball center (s / 64)) (v2 - v1)⟫_ℝ ≤
        2 * (4096 * Cχ * (J + B / 2) *
          ((d1.source.source i).real (ball first s) + (d2.source.source i).real (ball center s)) +
          |K| * A ^ 2 * s ^ 2 * ((hausdorff n X).real (ball first s) +
            (hausdorff n X).real (ball center s))) ∧
      ∀ b : Euclidean n,
        ⟪b, e.heat.mass.massOperator (ball center (s / 49152)) b⟫_ℝ ≤
          ⟪poissonCoordinateLift b, M.massOperator (ball center (3 * (s / 49152)))
            (poissonCoordinateLift b)⟫_ℝ := by
  obtain ⟨C₀, hC₀, hcuts⟩ := hcutoff hn
  refine ⟨C₀, hC₀, ?_⟩
  intro base first center a B J C A Cχ enlargement zeta eta Cg D Ca ker hk hA hCχ
    e hcenter d1 d2 i s f U v1 v2 hroom
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : s ≤ e.heat.radius := by
    have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
    change 2 * s ≤ e.heat.radius at hh
    linarith
  have hsub : ball center (s / 4) ⊆ ball base (32 * e.heat.radius) := by
    intro x hx
    have htri := dist_triangle x center base
    have hxc := mem_ball.mp hx
    have hcp := mem_ball.mp hcenter
    change dist x base < 32 * e.heat.radius
    linarith
  have hu : ∀ j, IsSobolevHarmonicOn μ hQ (ball center (s / 4)) (e.heat.coordinates j) :=
    fun j => (e.heat.splitting.harmonic j).mono μ hQ hsub
  have hgrad : ∀ j, ∀ᵐ x ∂μ.restrict (ball center (s / 4)),
      localGamma μ hQ (e.heat.coordinates j) (e.heat.coordinates j) x ≤ (1 + (1 : ℝ)) ^ 2 := by
    intro j
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (e.heat.splitting.gradient j)]
      with x hx
    exact hx.trans (by nlinarith [e.heat.initialError_pos, e.heat.initialError_le_one])
  have hf1 := d1.gradient i center hroom
  have hf2 := d2.gradient i center (by simp only [dist_self]; positivity)
  obtain ⟨L, _hL, M, henergy, hshift, _hpair⟩ := actual_poisson_pair_span hX hhessian
    (abs_nonneg K) (neg_abs_le K) hA (by norm_num : (0 : ℝ) ≤ 1)
    first center center d1.source d2.source d1.replacement d2.replacement i hroom
    (by simp only [dist_self]; positivity) e.heat.coordinates hu hgrad hf1 hf2
  have hv1 : U v1 = d1.replacement.replacement i := poissonSpanMap_right μ hQ e.heat.coordinates f 0
  have hv2 : U v2 = d2.replacement.replacement i := poissonSpanMap_right μ hQ e.heat.coordinates f 1
  let ell := poissonSpanLaplacian n ((n : ℝ) + |K| * (4 * s) ^ 2)
  have hell1 : ell v1 = (n : ℝ) + |K| * (4 * s) ^ 2 := poissonSpanLaplacian_right _ 0
  have hell2 : ell v2 = (n : ℝ) + |K| * (4 * s) ^ 2 := poissonSpanLaplacian_right _ 1
  let : IsFiniteMeasure (μ.restrict (ball center (2 * (s / 32)))) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hsmall : ball center (2 * (s / 32)) ⊆ ball center (s / 4) :=
    ball_subset_ball (by linarith)
  have hmass := actual_poisson_difference_mass_le μ hQ d1.replacement d2.replacement i
    (abs_nonneg K) hCχ hroom (by simp only [dist_self]; positivity) ell
    (Classical.choice (henergy v1)) (Classical.choice (henergy v2)) hv1 hv2 hell1 hell2 hshift
    (d2.cutoff i)
    (by simpa only [mul_pow] using ae_restrict_of_ae_restrict_of_subset hsmall hf1)
    (by simpa only [mul_pow] using ae_restrict_of_ae_restrict_of_subset hsmall hf2)
  dsimp only at hmass
  rw [M.measure_real _ _ measurableSet_ball] at hmass
  refine ⟨L, M, henergy, hmass, ?_⟩
  have hheat : ball center (2 * (s / 32)) ⊆ ball base (2 * (4 * e.heat.radius)) := by
    intro x hx
    have htri := dist_triangle x center base
    have hxc := mem_ball.mp hx
    have hcp := mem_ball.mp hcenter
    change dist x base < 2 * (4 * e.heat.radius)
    linarith
  have hcurv : -1 ≤ K * (s / 49152) ^ 2 := by
    have hsq : (s / 49152) ^ 2 ≤ e.heat.radius ^ 2 := by nlinarith [e.heat.radius_pos]
    have habs := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    have hlo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (s / 49152))
    have hc := e.curvature
    nlinarith
  let χ := Classical.choice (hcuts center (s / 49152) (by positivity) hcurv)
  intro b
  have G := (e.heat.energy b).restrict μ hQ hheat
  exact G.mass_le_of_same_energy μ hQ (Classical.choice (henergy (poissonCoordinateLift b)))
    χ (by positivity) (by linarith) (by
      rw [poissonSpanMap_lift μ hQ e.heat.coordinates f b])

end RegularPointCoordinates

end

end OAI
