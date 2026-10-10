import OAI.Geometry.RCD.Coordinates.RegularIterationPairs
import OAI.Geometry.RCD.Coordinates.IterationOpenness

namespace OAI

/-! # The chart limit of the regular-neighborhood iteration

Scalar smallness and geometric patch estimates yield an open chart with
two-sided ambient-distance bounds.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Once the scalar tolerances are met, the actual heat-coordinate
iteration has an open ambient-distance bi-Lipschitz limit chart. -/
theorem regular_iteration_limit_chart {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (psi : EuclideanGevreyCutoff n) {Cpin Theta : ℝ} (hCpin : 0 ≤ Cpin) (hTheta : 1 ≤ Theta) :
    let N := patchOverlapBound n (1 / 2) 2 3
    let Lcut := psi.constant * 536870912
    let Kcut := Lcut ^ 2 + 4 * Lcut ^ 3
    let Bjet := patchJetBase N (Real.sqrt (3 * Cpin)) Lcut
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
        {ker : ℝ → X → X → ℝ}
        {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
        (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta),
      0 ≤ zeta → zeta ≤ 1 / 2048 →
      (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹) * zeta) ≤ 3 / 4 →
      (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4 →
      zeta * iterationPairMultiplier Theta Bjet 64 ≤ 2097152 →
      ∀ (Ω : Set (Euclidean n)), IsOpen Ω →
      ∀ (u : e.heat.patchRegion ≃ₜ Ω), (∀ q, (u q).val = e.heat.values q.val) →
      ∀ (inverse : Euclidean n → {q : X // q ∈ ball base (e.heat.radius / 32)}),
      (∀ x ∈ Ω, (inverse x).val ∈ e.heat.patchRegion ∧ e.heat.values (inverse x).val = x) →
      ∀ g : PatchIterationGeometry (ι := X) Ω (distanceSourceRadius e.heat.radius e.heat.shift)
        Theta epsilon N (3 * Cpin) Kcut Lcut,
      g.frozen = (fun i x => e.heat.frozenAt (inverse x).val i) → HasOpenBilipschitzChart n base := by
  intro N Lcut Kcut Bjet
  let Fiter := patchAssemblyCoefficient N (3 * Cpin) Kcut Lcut
  have hLcut : 1 ≤ Lcut := by
    have h := psi.constant_ge_one
    dsimp only [Lcut]
    linarith
  have hKcut : 0 ≤ Kcut := by dsimp only [Kcut]; positivity
  have hFiter : 1 ≤ Fiter := (patchAssemblyCoefficient_bounds N (C := 3 * Cpin) hKcut hLcut).1
  have hBjet : 1 ≤ Bjet := patchJetBase_ge_one hLcut
  obtain ⟨epsilon, hepsilon, hepsilon1, hchart⟩ := exists_analytic_iteration_open_limit_chart
    (X := X) hTheta hFiter hBjet (by norm_num : (1 : ℝ) ≤ 64)
  refine ⟨epsilon, hepsilon, hepsilon1, ?_⟩
  intro base a κ B J C A Cχ enlargement zeta eta ker hk e hzeta hzetaSmall hgram hnear hzetaL
    Ω hΩ u hu inverse hinverse g hg
  let r0 := distanceSourceRadius e.heat.radius e.heat.shift
  let L := iterationPairMultiplier Theta Bjet 64
  have hr0 : 0 < r0 := distanceSourceRadius_pos e.heat.radius_pos _
  have hL : 0 < L := by
    dsimp only [L, iterationPairMultiplier, iterationChartRatio]
    positivity
  let δ := min (e.heat.radius / 2 ^ (e.heat.shift + 12)) (r0 / (4 * L))
  have hδ : 0 < δ := lt_min (div_pos e.heat.radius_pos (by positivity)) (by positivity)
  have hδrad : δ ≤ e.heat.radius / 2 ^ (e.heat.shift + 12) := min_le_left _ _
  have hδdiam : 2 * L * δ ≤ r0 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * L)).mp (min_le_right _ _ : δ ≤ r0 / (4 * L))
    nlinarith [mul_nonneg hL.le hδ.le]
  have hsubset : ball base δ ⊆ e.heat.patchRegion := by
    apply ball_subset_ball
    exact hδrad.trans (div_le_div_of_nonneg_left e.heat.radius_pos.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega : e.heat.shift + 10 ≤ e.heat.shift + 12)))
  obtain ⟨hO, v, hv⟩ := restrict_open_coordinate_chart isOpen_ball hΩ hsubset e.heat.values u hu
  have hOΩ : Set.range (fun x : ball base δ => e.heat.values x.val) ⊆ Ω := by
    rintro _ ⟨x, rfl⟩
    change e.heat.values x.val ∈ Ω
    rw [← hu ⟨x.val, hsubset x.property⟩]
    exact (u ⟨x.val, hsubset x.property⟩).property
  let d := g.toCanonicalAnalyticIterationData hr0 hepsilon.le hepsilon1
    (by positivity) hKcut hLcut
  have hvfun : (fun x : ball base δ => (v x).val) = fun x => e.heat.values x.val := funext hv
  have hgeom : IterationPairGeometry (fun x : ball base δ => (v x).val) Ω d.frozen r0 Theta Bjet 64 := by
    change IterationPairGeometry _ Ω g.frozen r0 Theta Bjet 64
    rw [hvfun, hg]
    exact regular_iteration_pair_geometry hX e hzeta hzetaSmall hgram hnear u hu inverse hinverse
      hTheta hBjet hzetaL hδrad hδdiam
  exact hchart base Ω hΩ (ball base δ) isOpen_ball (mem_ball_self hδ)
    (Set.range (fun x : ball base δ => e.heat.values x.val)) hO hOΩ v r0 hr0 d hgeom

end RegularPointCoordinates

end

end OAI
