import OAI.Geometry.RCD.Sobolev.CompactMeasureLaplacian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-!
# The heat identity for a full compactly supported signed Laplacian

The distributional source is paired with continuous positive-time kernel
rows. Locality supplies the compact test, and the actual L2 heat equation
supplies the derivative. This proves the positive-endpoint measure-source
identity without assuming absolute continuity of the source.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

include hp in
/-- Pointwise time differentiation of the continuous representative of
heat flow from actual Sobolev data. -/
theorem kernelHeat_hasDerivAt (u : SobolevSpace μ hQ) {t : ℝ}
    (ht : 0 < t) (x : X) :
    HasDerivAt (fun s => kernelHeat μ hQ hp s (SobolevSpace.toLp μ hQ u) x)
      (-energyForm μ hQ u (heatKernelSobolev μ hQ hp t ht x)) t := by
  let a := t / 2
  have ha : 0 < a := half_pos ht
  have hta : 0 < t - a := by dsimp [a]; linarith
  let f := heatKernelRow μ hQ hp a x
  have hd := (heatAt_inner_lp_hasDerivAt μ hQ f u (t - a) hta).scomp t
    ((hasDerivAt_id t).sub_const a)
  simp only [one_smul] at hd
  have he : heatSobolev μ hQ (t - a) hta f = heatKernelSobolev μ hQ hp t ht x := by
    have hLp : SobolevSpace.toLp μ hQ (heatSobolev μ hQ (t - a) hta f) =
        SobolevSpace.toLp μ hQ (heatKernelSobolev μ hQ hp t ht x) := by
      rw [heatSobolev_toLp, heatKernelSobolev_toLp, heatKernelRow_evolves μ hQ hp hta ha]
      simp only [sub_add_cancel]
    exact Subtype.ext hLp
  rw [he, energyForm_comm μ hQ] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show a < t by dsimp [a]; linarith)] with s hs
  dsimp [kernelHeat]
  rw [heatKernelRow_evolves μ hQ hp (sub_pos.mpr hs) ha]
  simp only [sub_add_cancel]

/-- The pointwise derivative against the full signed source. -/
theorem IsMeasureLaplacian.kernelHeat_hasDerivAt
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    {t : ℝ} (ht : 0 < t) (x : X) :
    HasDerivAt (fun s => kernelHeat μ hQ hp s (SobolevSpace.toLp μ hQ u) x)
      (∫ᵛ z, p t x z ∂<•ν) t := by
  have hd := RegularPointCoordinates.kernelHeat_hasDerivAt μ hQ hp u ht x
  rw [hν.test_heatKernel μ hQ hp c hR hu hsν ht x, neg_neg] at hd
  exact hd

/-- The manuscript's positive-endpoint semigroup identity for compact
measure sources, using continuous representatives and the full measure. -/
theorem IsMeasureLaplacian.kernelHeat_sub_eq_integral
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : X) :
    kernelHeat μ hQ hp t (SobolevSpace.toLp μ hQ u) x -
      kernelHeat μ hQ hp s (SobolevSpace.toLp μ hQ u) x =
      ∫ r in s..t, (∫ᵛ z, p r x z ∂<•ν) := by
  let a := s / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let φ := fun r => heatTail μ hQ a ha (heatKernelRow μ hQ hp a x) (r - a)
  have hφc : Continuous φ := by
    exact (heatSobolevMap μ hQ a ha).continuous.comp
      ((heatAt_continuous μ hQ (heatKernelRow μ hQ hp a x)).comp
        ((continuous_id.sub continuous_const).sub continuous_const))
  have hφ (r : ℝ) (hr : r ∈ Icc s t) :
      φ r = heatKernelSobolev μ hQ hp r (hs.trans_le hr.1) x := by
    have hlow : s ≤ r := hr.1
    have hLp : SobolevSpace.toLp μ hQ (φ r) =
        SobolevSpace.toLp μ hQ (heatKernelSobolev μ hQ hp r (hs.trans_le hr.1) x) := by
      change SobolevSpace.toLp μ hQ (heatTail μ hQ a ha _ (r - a)) =
        SobolevSpace.toLp μ hQ (heatKernelSobolev μ hQ hp r (hs.trans_le hr.1) x)
      rw [heatTail_toLp μ hQ a ha _ (r - a) (by dsimp [a]; linarith),
        heatKernelSobolev_toLp,
        heatKernelRow_evolves μ hQ hp (show 0 < r - a by dsimp [a]; linarith) ha]
      simp only [sub_add_cancel]
    exact Subtype.ext hLp
  let D := fun r => -energyForm μ hQ u (φ r)
  have hDc : Continuous D :=
    ((energyForm_continuous μ hQ).comp (continuous_const.prodMk hφc)).neg
  have hDe (r : ℝ) (hr : r ∈ Icc s t) : D r = ∫ᵛ z, p r x z ∂<•ν := by
    dsimp only [D]
    rw [hφ r hr, hν.test_heatKernel μ hQ hp c hR hu hsν, neg_neg]
  have hFc : ContinuousOn
      (fun r => kernelHeat μ hQ hp r (SobolevSpace.toLp μ hQ u) x) (Icc s t) := by
    intro r hr
    exact (RegularPointCoordinates.kernelHeat_hasDerivAt μ hQ hp u (hs.trans_le hr.1) x).continuousAt.continuousWithinAt
  have hd (r : ℝ) (hr : r ∈ Ioo s t) :
      HasDerivAt (fun r => kernelHeat μ hQ hp r (SobolevSpace.toLp μ hQ u) x) (D r) r := by
    rw [hDe r ⟨hr.1.le, hr.2.le⟩]
    exact hν.kernelHeat_hasDerivAt μ hQ hp c hR hu hsν (hs.trans hr.1) x
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hFc hd
    (hDc.intervalIntegrable s t)
  rw [← he]
  apply intervalIntegral.integral_congr
  intro r hr
  exact hDe r (by simpa only [uIcc_of_le hst] using hr)

end RegularPointCoordinates

end

end OAI
