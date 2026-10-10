import OAI.Geometry.RCD.Coordinates.RegularPairMass
import OAI.Geometry.RCD.Sobolev.PoissonMassUnits
import OAI.Geometry.RCD.Metric.FullMassScaling

namespace OAI

/-! # The full original heat mass in scale-independent source units -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

def regularPinchingMassConstant (n : ℕ) (Ccut A B J Cχ Q L : ℝ) : ℝ :=
  8 * (4096 * Cχ * (J + B / 2) + A ^ 2) +
    4 * ((Ccut * (49152 : ℝ) ^ 2 / 18 + 1) * ((5 / 4 : ℝ) * euclideanUnitVolume n)) *
      (Q ^ 2 + 16 * (n : ℝ) ^ 2 *
        (4 * ((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * L ^ 2 + Q ^ 2))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Both terms of the actual mass estimate are controlled by the same
squared source. The constant has no dependence on center or scale. -/
theorem regular_pair_mass_scaling {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base first center : X} {a B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a |K| B J C A Cχ enlargement zeta eta)
    (hcenter : center ∈ ball base (e.heat.radius / 32))
    (d1 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca first)
    (d2 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca center)
    {Ccut Q L sigma : ℝ} (hCcut : 0 ≤ Ccut) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ)
    (i : ℕ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let rho := s / 49152
    let Rvol := (5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹
    let Praw := 2 * (4096 * Cχ * (J + B / 2) *
      ((d1.source.source i).real (ball first s) + (d2.source.source i).real (ball center s)) +
      |K| * A ^ 2 * s ^ 2 * (μ.real (ball first s) + μ.real (ball center s)))
    let Fcut := ((Ccut / (3 * rho) ^ 2) / 2 + |K|) * μ.real (closedBall center (6 * rho))
    normalizedPoissonDefect μ hX.quadratic d1.source i +
      normalizedPoissonDefect μ hX.quadratic d2.source i ≤ sigma ^ 2 →
    4 * (Praw + Fcut * (Q ^ 2 * s ^ 2 * sigma ^ 2)) +
      4 * (Fcut * (16 * (n : ℝ) ^ 2)) *
        ((2 * Real.sqrt Rvol * (L * s * sigma)) ^ 2 + Q ^ 2 * s ^ 2 * sigma ^ 2) ≤
      regularPinchingMassConstant n Ccut A B J Cχ Q L * s ^ n * sigma ^ 2 := by
  intro μ s rho Rvol Praw Fcut hsource
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : 2 * s ≤ e.heat.radius := distanceSourceRadius_outer_le e.heat.radius_pos.le i
  let Cs := 4096 * Cχ * (J + B / 2) + A ^ 2
  let Cv := (5 / 4 : ℝ) * euclideanUnitVolume n
  let Cf := (Ccut * (49152 : ℝ) ^ 2 / 18 + 1) * Cv
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  have hCv : 0 ≤ Cv := by dsimp only [Cv]; exact mul_nonneg (by norm_num) (euclideanUnitVolume_pos n).le
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  have hRvol : 0 ≤ Rvol := by dsimp only [Rvol]; positivity
  have hP : Praw ≤ 2 * Cs * s ^ n * sigma ^ 2 := by
    have hh := poisson_pair_mass_units μ hX.quadratic d1.source d2.source (abs_nonneg K)
      (by positivity : 0 ≤ 4096 * Cχ * (J + B / 2)) i (A := A)
    dsimp only at hh
    rw [Real.rpow_natCast] at hh
    apply hh.trans
    change 2 * Cs * s ^ n * _ ≤ _
    gcongr
  have hcurv : |K| * s ^ 2 ≤ 1 := by
    have hsq : s ^ 2 ≤ e.heat.radius ^ 2 := by nlinarith [e.heat.radius_pos]
    have hh := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    have hc := e.curvature
    nlinarith [mul_nonneg (abs_nonneg K) (sq_nonneg e.heat.radius)]
  have hvolume : μ.real (closedBall center (6 * rho)) ≤ Cv * s ^ n := by
    have hh := (quarter_volume_bounds hs (euclideanUnitVolume_pos n)
      (e.volume center hcenter s hs (by linarith))).2.2
    exact (measureReal_mono (closedBall_subset_ball (by dsimp only [rho]; linarith))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))).trans hh
  have hF : Fcut * s ^ 2 ≤ Cf * s ^ n :=
    scaled_cutoff_mass_factor hs hCcut (abs_nonneg K) hCv hcurv hvolume
  exact full_mass_scaling hs.le hCs hCf hRvol hP hF

end RegularPointCoordinates

end

end OAI
