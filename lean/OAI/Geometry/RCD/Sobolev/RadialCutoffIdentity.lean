import OAI.Geometry.RCD.Metric.InwardDistance
import OAI.Geometry.RCD.Coordinates.VolumeProfileRegularity

namespace OAI

/-!
# Exact volume-drop identity for the radial test

The weak squared-distance pairing is integrated against the explicit radial
power test. Its combination with `n` times the test is exactly the difference
of the two normalized ball indicators. Positive source mass will therefore
be controlled by the actual volume drop, including its sign.
-/

open Set Metric MeasureTheory Filter
open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X]

/-- The continuous representative of the Sobolev radial test. -/
def radialPowerRep (n r R : ℝ) (c : X) (x : X) : ℝ :=
  radialPowerPrimitive n r R (positiveClip (R - r) (inwardDistance c R x))

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
 theorem radialPowerRep_lipschitz {n r R : ℝ} (hn : 0 < n) (hr : 0 < r) (c : X) :
    LipschitzWith ⟨r ^ (-(n + 1)), Real.rpow_nonneg hr.le _⟩ (radialPowerRep n r R c) := by
  change LipschitzWith _
    (radialPowerPrimitive n r R ∘ positiveClip (R - r) ∘ inwardDistance c R)
  apply ((radialPowerPrimitive_lipschitz (R := R) hn hr).comp
    ((positiveClip_lipschitz (R - r)).comp (inwardDistance_lipschitz c R))).weaken
  change r ^ (-(n + 1)) * (1 * 1) ≤ r ^ (-(n + 1))
  simp only [mul_one, le_refl]

omit [MeasurableSpace X] [BorelSpace X] in
 theorem radialPowerRep_compact {n r R : ℝ} (hrR : r ≤ R) (c : X) :
    HasCompactSupport (radialPowerRep n r R c) := by
  exact ((inwardDistance_compact c R).comp_left (positiveClip_zero (sub_nonneg.mpr hrR))).comp_left
    (radialPowerPrimitive_zero n r R)

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
 theorem radialPowerRep_zero {n r R : ℝ} (hrR : r ≤ R) (c x : X) (hx : R ≤ dist c x) :
    radialPowerRep n r R c x = 0 := by
  simp only [radialPowerRep, inwardDistance, max_eq_right (sub_nonpos.mpr hx),
    positiveClip_zero (sub_nonneg.mpr hrR), radialPowerPrimitive_zero]

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
 theorem radialPowerRep_inner {n r R : ℝ} (hn : 0 < n) (hr : 0 < r) (hrR : r ≤ R)
    (c x : X) (hx : dist c x ≤ r) :
    radialPowerRep n r R c x = (r ^ (-n) - R ^ (-n)) / n := by
  have hd : 0 ≤ R - dist c x := sub_nonneg.mpr (hx.trans hrR)
  simp only [radialPowerRep, inwardDistance, positiveClip,
    max_eq_left hd, min_eq_right (by linarith : R - r ≤ R - dist c x)]
  simpa only [sub_sub_cancel] using radialPowerPrimitive_formula hn hr (sub_nonneg.mpr hrR) le_rfl

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
 theorem radialPowerRep_annulus {n r R : ℝ} (hn : 0 < n) (hr : 0 < r)
    (c x : X) (hrx : r ≤ dist c x) (hxR : dist c x ≤ R) :
    radialPowerRep n r R c x = ((dist c x) ^ (-n) - R ^ (-n)) / n := by
  have hd := sub_nonneg.mpr hxR
  simp only [radialPowerRep, inwardDistance, positiveClip,
    max_eq_left hd, min_eq_left (by linarith : R - dist c x ≤ R - r)]
  simpa only [sub_sub_cancel] using radialPowerPrimitive_formula hn hr hd
    (by linarith : R - dist c x ≤ R - r)

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem radialPowerTest_inward_coe {n r R : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hrR : r ≤ R) (c : X) :
    SobolevSpace.toLp μ hQ (radialPowerTest μ hQ (inwardSobolev μ hQ c R) hn hr hrR) =ᵐ[μ]
      radialPowerRep n r R c := by
  filter_upwards [radialPowerTest_coe μ hQ (inwardSobolev μ hQ c R) hn hr hrR,
    inwardSobolev_coe μ hQ c R] with x ht hu
  rw [ht, hu]
  rfl

/-- The pointwise cancellation on the annulus, and constancy on the inner ball. -/
theorem radialPowerTest_indicator_identity {n r R : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hrR : r < R) (c : X) (q : SobolevSpace μ hQ)
    (hpair : ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ q (inwardSobolev μ hQ c R) x = -dist c x)
    (hsphere : μ (sphere c r) = 0) :
    (fun x => n * radialPowerRep n r R c x +
      localGamma μ hQ q (radialPowerTest μ hQ (inwardSobolev μ hQ c R) hn hr hrR.le) x) =ᵐ[μ]
      fun x => (ball c r).indicator (fun _ => r ^ (-n)) x -
        (ball c R).indicator (fun _ => R ^ (-n)) x := by
  have hR : 0 ≤ R := (hr.trans hrR).le
  have hnot : ∀ᵐ x ∂μ, x ∉ sphere c r := by
    exact measure_eq_zero_iff_ae_notMem.mp hsphere
  filter_upwards [radialPowerTest_gamma μ hQ q (inwardSobolev μ hQ c R)
      ((inwardSobolev_bounds μ hQ c hR).mono (fun _ hx => hx.1)) hn hr hrR.le,
    inwardSobolev_coe μ hQ c R, hpair, hnot,
    localGamma_comm μ hQ q (inwardSobolev μ hQ c R),
    localGamma_zero_on_level μ hQ (inwardSobolev μ hQ c R) q 0] with x hg hu hp hnosp hc hz
  have hne : dist c x ≠ r := by simpa only [mem_sphere, dist_comm] using hnosp
  by_cases hxR : dist c x < R
  · have hmemR : x ∈ ball c R := by simpa only [mem_ball, dist_comm] using hxR
    have hi : inwardDistance c R x = R - dist c x := by
      exact max_eq_left (sub_nonneg.mpr hxR.le)
    rw [hg, hu, hi]
    by_cases hxr : dist c x < r
    · have hmemr : x ∈ ball c r := by simpa only [mem_ball, dist_comm] using hxr
      rw [ite_eq_right (by linarith), radialPowerRep_inner hn hr hrR.le c x hxr.le,
        indicator_of_mem hmemr, indicator_of_mem hmemR]
      field_simp
      ring
    · have hrl : r < dist c x := lt_of_le_of_ne (le_of_not_gt hxr) hne.symm
      have hnmemr : x ∉ ball c r := by simpa only [mem_ball, dist_comm, not_lt] using hrl.le
      rw [ite_eq_left (by linarith), hp hmemR,
        radialPowerRep_annulus hn hr c x hrl.le hxR.le,
        indicator_of_notMem hnmemr, indicator_of_mem hmemR]
      have hw : radialPowerWeight n r R (R - dist c x) * dist c x = (dist c x) ^ (-n) := by
        have hid : R - (R - dist c x) = dist c x := by ring
        rw [radialPowerWeight, hid, max_eq_right hrl.le]
        calc
          _ = (dist c x) ^ (-(n + 1)) * (dist c x) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (dist c x) ^ (-(n + 1) + 1) := (Real.rpow_add (hr.trans hrl) _ _).symm
          _ = _ := by congr 1; ring
      rw [mul_neg, hw]
      field_simp
      ring
  · have hRx := le_of_not_gt hxR
    have hnmemR : x ∉ ball c R := by simpa only [mem_ball, dist_comm, not_lt] using hRx
    have hnmemr : x ∉ ball c r := by
      simpa only [mem_ball, dist_comm, not_lt] using hrR.le.trans hRx
    have hi : inwardDistance c R x = 0 := max_eq_right (sub_nonpos.mpr hRx)
    have hz' : localGamma μ hQ q (inwardSobolev μ hQ c R) x = 0 := hc.trans (hz (hu.trans hi))
    rw [hg, hu, hi, ite_eq_left (sub_pos.mpr hrR), hz', mul_zero,
      radialPowerRep_zero hrR.le c x hRx, indicator_of_notMem hnmemr, indicator_of_notMem hnmemR]
    ring

/-- Integrating the cancellation gives the actual normalized volume drop. -/
theorem radialPowerTest_volume_identity {n r R : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hrR : r < R) (c : X) (q : SobolevSpace μ hQ)
    (hpair : ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ q (inwardSobolev μ hQ c R) x = -dist c x)
    (hsphere : μ (sphere c r) = 0) :
    n * (∫ x, radialPowerRep n r R c x ∂μ) +
      energyForm μ hQ q (radialPowerTest μ hQ (inwardSobolev μ hQ c R) hn hr hrR.le) =
      r ^ (-n) * μ.real (ball c r) - R ^ (-n) * μ.real (ball c R) := by
  have hi : Integrable (radialPowerRep n r R c) μ :=
    (radialPowerRep_lipschitz hn hr c).continuous.integrable_of_hasCompactSupport
      (radialPowerRep_compact hrR.le c)
  have hγ := localGamma_memL1 μ hQ q
    (radialPowerTest μ hQ (inwardSobolev μ hQ c R) hn hr hrR.le)
  have he := integral_congr_ae (radialPowerTest_indicator_identity μ hQ hn hr hrR c q hpair hsphere)
  rw [integral_add (hi.const_mul n) hγ, integral_const_mul,
    integral_localGamma_eq_energyForm] at he
  rw [integral_sub ((integrableOn_const (measure_ball_lt_top.ne)).integrable_indicator isOpen_ball.measurableSet)
    ((integrableOn_const (measure_ball_lt_top.ne)).integrable_indicator isOpen_ball.measurableSet),
    integral_indicator_const _ isOpen_ball.measurableSet,
    integral_indicator_const _ isOpen_ball.measurableSet, smul_eq_mul, smul_eq_mul] at he
  simpa only [mul_comm] using he

end RegularPointCoordinates

end

end OAI
