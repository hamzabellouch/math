import OAI.Geometry.RCD.Sobolev.RadialCutoffMass

namespace OAI

/-!
# Applying the radial test to an actual squared-distance representative

The squared-distance function is cut off only at the larger working radius.
Locality transfers its radial pairing to each smaller ball. The resulting
mass estimate takes precisely the local weak Laplacian-defect identity and
the eikonal input, rather than an assumed annular source formula.
-/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem inwardQuadratic_gamma_smaller (c : X) {R T : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T)
    (heik : ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ (inwardSobolev μ hQ c R) (inwardSobolev μ hQ c R) x = 1) :
    ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ (inwardQuadratic μ hQ c (hR.trans hRT)) (inwardSobolev μ hQ c R) x =
        -dist c x := by
  let u := inwardSobolev μ hQ c R
  let w := inwardSobolev μ hQ c T
  have hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ (⟨T, hR.trans hRT⟩ : ℝ≥0) := by
    filter_upwards [inwardSobolev_bounds μ hQ c (hR.trans hRT)] with x hx
    change |SobolevSpace.toLp μ hQ (inwardSobolev μ hQ c T) x| ≤ T
    simpa only [abs_of_nonneg hx.1] using hx.2
  filter_upwards [heik, inwardSobolev_coe μ hQ c R, inwardSobolev_coe μ hQ c T,
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ w) (SobolevSpace.toLp μ hQ u),
    localGamma_sub_left μ hQ w u u,
    localGamma_zero_on_level μ hQ (w - u) u (T - R),
    localGamma_sub_left μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ w ⟨T, hR.trans hRT⟩) (T • w) u,
    localGamma_smul_left μ hQ (1 / 2 : ℝ) (SobolevSpace.square μ hQ w ⟨T, hR.trans hRT⟩) u,
    localGamma_smul_left μ hQ T w u,
    localGamma_square μ hQ w u ⟨T, hR.trans hRT⟩ hb] with x he hu hw hsub hγsub hz hs ha ht hsq hx
  have hd : dist c x < R := by simpa only [mem_ball, dist_comm] using hx
  have hu' : SobolevSpace.toLp μ hQ u x = R - dist c x :=
    hu.trans (max_eq_left (sub_nonneg.mpr hd.le))
  have hw' : SobolevSpace.toLp μ hQ w x = T - dist c x :=
    hw.trans (max_eq_left (sub_nonneg.mpr (hd.le.trans hRT)))
  have hdif : SobolevSpace.toLp μ hQ (w - u) x = T - R := by
    change (SobolevSpace.toLp μ hQ w - SobolevSpace.toLp μ hQ u) x = _
    simp only [hsub, Pi.sub_apply, hu', hw']
    ring
  have hp : localGamma μ hQ w u x = 1 := by
    have hz' := hz hdif
    rw [hγsub, he hx] at hz'
    linarith
  change localGamma μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ w ⟨T, hR.trans hRT⟩ - T • w) u x = _
  rw [hs, ha, ht, hsq, hp, hw']
  ring

/-- The actual positive squared-distance defect satisfies the volume-drop
bound on an inner ball. Its two published inputs are the local weak defect
identity and the distance eikonal property. Bishop--Gromov removes the sphere
exception. -/
theorem squaredDistance_source_mass_le {n r R T curvature : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hrR : r < R) (hRT : R < T)
    (hcurvature : 0 ≤ curvature) (c : X) (σ : Measure X) [IsFiniteMeasure σ]
    {model : ℝ → ℝ} (hBG : BallVolumeComparison μ model) (hmodelcont : Continuous model)
    (hmodelr : 0 < model r)
    (heik : ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ (inwardSobolev μ hQ c R) (inwardSobolev μ hQ c R) x = 1)
    (hdefect : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
      LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ ball c T →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ (inwardQuadratic μ hQ c ((hr.trans hrR).trans hRT).le) ψ +
        (n + curvature) * (∫ x, v x ∂μ) = ∫ x, v x ∂σ) :
    ((r ^ (-n) - R ^ (-n)) / n) * σ.real (ball c r) ≤
      r ^ (-n) * μ.real (ball c r) - R ^ (-n) * μ.real (ball c R) +
      curvature * ((r ^ (-n) - R ^ (-n)) / n) * μ.real (ball c R) := by
  apply radial_source_cutoff_mass_le μ hQ hn hr hrR hRT hcurvature c _ σ hdefect
  · exact inwardQuadratic_gamma_smaller μ hQ c (hr.trans hrR).le hRT.le heik
  · exact sphere_measure_zero_of_comparison hBG hmodelcont c hr hmodelr

end RegularPointCoordinates

end

end OAI
