import OAI.Geometry.RCD.Coordinates.RegularPairProjection
import OAI.Geometry.RCD.Sobolev.PoissonProjectionGradient

namespace OAI

/-! # Harmonic residual gradients in the common regular neighborhood -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual sharp projection bound supplies an actual Sobolev residual
and a uniform physical gradient estimate, in the same centered heat frame. -/
theorem regular_pair_projection_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {P : ℝ} (hP : 0 < P) :
    ∃ Q : ℝ, 0 < Q ∧
    ∀ {base first center : X} {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker},
    0 ≤ κ →
    ∀ (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta),
    center ∈ ball base (e.heat.radius / 32) →
    ∀ (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
      (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center) (i : ℕ),
    let s := distanceSourceRadius e.heat.radius i
    let uc := centeredColumn (hausdorff n X) hX.quadratic
      (transformedColumn (hausdorff n X) hX.quadratic e.heat.coordinates (d2.frame i))
      ((d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev
    dist center first ≤ s / 4 → ∀ source : ℝ, 0 ≤ source →
    regularPairProjectionSize hX e d1 d2 i ≤ P * source →
    ∃ (c : ℝ) (b : Euclidean n) (w : SobolevSpace (hausdorff n X) hX.quadratic),
      w = d2.replacement.replacement i - d1.replacement.replacement i -
        (c • e.one.sobolev + sobolevColumnMap (hausdorff n X) hX.quadratic uc b) ∧
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball center ((1 / 2048) * s)) w ∧
      ∀ᵐ x ∂(hausdorff n X).restrict (ball center ((1 / 4096) * s)),
        localGamma (hausdorff n X) hX.quadratic w w x ≤ Q ^ 2 * s ^ 2 * source ^ 2 := by
  obtain ⟨Q, hQ, hbound⟩ := poisson_projection_gradient hX hgradient hn hP
  refine ⟨Q, hQ, ?_⟩
  intro base first center a κ B J C A Cχ enlargement zeta eta Cg D Ca ker hk hκ
    e hcenter d1 d2 i s uc hroom source hsource hsize
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : s ≤ e.heat.radius := by
    have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
    change 2 * s ≤ e.heat.radius at hh
    linarith
  have hsq : s ^ 2 ≤ e.heat.radius ^ 2 := by nlinarith [e.heat.radius_pos]
  have habs := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
  have hlo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg s)
  have he := e.curvature
  have hkR := mul_nonneg hκ (sq_nonneg e.heat.radius)
  have hcurv : -1 ≤ K * s ^ 2 := by nlinarith
  have hone := e.oneRepresentative center hcenter i
  have hfirst := (d2.splitting i).center (hausdorff n X) hX.quadratic
    ((d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center))
    e.one.sobolev hone
  have hsub : ball center ((1 / 2048) * s) ⊆ ball center (2 * s) :=
    ball_subset_ball (by linarith)
  obtain ⟨c, b, w, hw, hharm, _, hgrad⟩ := hbound d1.source d2.source
    d1.replacement d2.replacement i hroom hcurv uc e.one.sobolev
    (fun j => (hfirst.harmonic j).mono (hausdorff n X) hX.quadratic hsub)
    (ae_restrict_of_ae_restrict_of_subset hsub hone) source hsource hsize
  exact ⟨c, b, w, hw, hharm, hgrad⟩

end RegularPointCoordinates

end

end OAI
