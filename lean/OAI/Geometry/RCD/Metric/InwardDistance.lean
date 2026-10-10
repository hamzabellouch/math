import OAI.Geometry.RCD.Sobolev.RadialPowerTest

namespace OAI

/-!
# Compact inward distance and its squared-distance primitive

The inward distance to the boundary of a metric ball is a compactly supported
Lipschitz function. Its quadratic primitive agrees with squared distance,
up to a constant, on the ball. This realizes radial tests in the global
Sobolev space without pretending the unbounded distance itself is in L2.
-/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

def inwardDistance (c : X) (R : ℝ) (x : X) : ℝ := max (R - dist c x) 0

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
theorem inwardDistance_lipschitz (c : X) (R : ℝ) :
    LipschitzWith 1 (inwardDistance c R) := by
  have h : LipschitzWith 1 (fun x : X => R - dist c x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm, NNReal.coe_one, one_mul]
      using dist_dist_dist_le_right c x y
  exact h.max_const 0

omit [MeasurableSpace X] [BorelSpace X] in
theorem inwardDistance_compact (c : X) (R : ℝ) : HasCompactSupport (inwardDistance c R) := by
  apply HasCompactSupport.intro (isCompact_closedBall c R)
  intro x hx
  apply max_eq_right
  have hd : R < dist c x := by simpa only [mem_closedBall, dist_comm, not_le] using hx
  linarith

def inwardSobolev (c : X) (R : ℝ) : SobolevSpace μ hQ :=
  SobolevSpace.ofLipschitzCompact μ hQ (inwardDistance_lipschitz c R) (inwardDistance_compact c R)

theorem inwardSobolev_coe (c : X) (R : ℝ) :
    SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R) =ᵐ[μ] inwardDistance c R :=
  SobolevSpace.ofLipschitzCompact_coe μ hQ _ _

theorem inwardSobolev_bounds (c : X) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R) x ∧
      SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R) x ≤ R := by
  filter_upwards [inwardSobolev_coe μ hQ c R] with x hx
  rw [hx]
  exact ⟨le_max_right _ _, max_le (sub_le_self _ dist_nonneg) hR⟩

/-- The primitive equals `dist²/2 - R²/2` inside the ball. -/
def inwardQuadratic (c : X) {R : ℝ} (hR : 0 ≤ R) : SobolevSpace μ hQ :=
  (1 / 2 : ℝ) • SobolevSpace.square μ hQ (inwardSobolev μ hQ c R) ⟨R, hR⟩ -
    R • inwardSobolev μ hQ c R

theorem inwardQuadratic_coe (c : X) {R : ℝ} (hR : 0 ≤ R) :
    SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ c hR) =ᵐ[μ]
      fun x => (inwardDistance c R x) ^ 2 / 2 - R * inwardDistance c R x := by
  have hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R) x| ≤ (⟨R, hR⟩ : ℝ≥0) := by
    filter_upwards [inwardSobolev_bounds μ hQ c hR] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  filter_upwards [inwardSobolev_coe μ hQ c R,
    SobolevSpace.square_coe μ hQ (inwardSobolev μ hQ c R) ⟨R, hR⟩ hb,
    Lp.coeFn_smul (1 / 2 : ℝ) (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ
      (inwardSobolev μ hQ c R) ⟨R, hR⟩)),
    Lp.coeFn_smul R (SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R)),
    Lp.coeFn_sub ((1 / 2 : ℝ) • SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ
      (inwardSobolev μ hQ c R) ⟨R, hR⟩))
      (R • SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R))] with x hu hs ha hb he
  change (((1 / 2 : ℝ) • SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ
      (inwardSobolev μ hQ c R) ⟨R, hR⟩)) -
      R • SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R)) x = _
  simp only [he, Pi.sub_apply, ha, hb, Pi.smul_apply, smul_eq_mul, hs, hu]
  ring

/-- Eikonal control of inward distance gives the required radial pairing.
The eikonal premise is the local distance consequence of Gigli (2015),
Corollary 5.15 and Theorem 5.3; it is not a source-mass estimate. -/
theorem inwardQuadratic_gamma (c : X) {R : ℝ} (hR : 0 ≤ R)
    (heik : ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ (inwardSobolev μ hQ c R) (inwardSobolev μ hQ c R) x = 1) :
    ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ (inwardQuadratic μ hQ c hR) (inwardSobolev μ hQ c R) x = -dist c x := by
  let u := inwardSobolev μ hQ c R
  have hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ (⟨R, hR⟩ : ℝ≥0) := by
    filter_upwards [inwardSobolev_bounds μ hQ c hR] with x hx
    change |SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c R) x| ≤ R
    simpa only [abs_of_nonneg hx.1] using hx.2
  filter_upwards [heik, inwardSobolev_coe μ hQ c R,
    localGamma_sub_left μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ u ⟨R, hR⟩) (R • u) u,
    localGamma_smul_left μ hQ (1 / 2 : ℝ) (SobolevSpace.square μ hQ u ⟨R, hR⟩) u,
    localGamma_smul_left μ hQ R u u,
    localGamma_square μ hQ u u ⟨R, hR⟩ hb] with x he hu hs ha hr hsq hx
  change localGamma μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ u ⟨R, hR⟩ - R • u) u x = _
  rw [hs, ha, hr, hsq, he hx, hu]
  have hd : dist c x < R := by simpa only [mem_ball, dist_comm] using hx
  simp only [inwardDistance, max_eq_left (sub_nonneg.mpr hd.le)]
  ring

end RegularPointCoordinates

end

end OAI
