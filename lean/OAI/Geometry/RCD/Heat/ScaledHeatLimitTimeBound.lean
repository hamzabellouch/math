import OAI.Geometry.RCD.Heat.ScaledHeatTimeBound
import OAI.Geometry.RCD.Metric.FixedGaugeLocalBounds
import OAI.Geometry.RCD.Heat.ScaledHeatGlobalCompactness

namespace OAI

/-! # Vanishing viscosity in the time increment estimate

This uses the prescribed global limit and subsequence. The constant in
the limiting bound depends only on the local cylinder, not on the test.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_limit_pairing_time_bound (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hconv : ∀ t ∈ Ioo δ 1, t ∉ N → TendstoUniformly
      (fun k (x : closedBall z r) => hX.fixedGaugeScaledPotential hn p ν
        (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x) (fun x => G t x) atTop) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ᵐ x ∂hausdorff n X, x ∉ closedBall z r →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x = 0) →
      ∀ Bφ : ℝ, (∀ᵐ x ∂hausdorff n X,
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x| ≤ Bφ) →
      ∀ s ∈ Ioo δ 1, s ∉ N → ∀ t ∈ Ioo δ 1, t ∉ N →
      |(∫ x in closedBall z r, SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x * G t x ∂hausdorff n X) -
        (∫ x in closedBall z r, SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x * G s x ∂hausdorff n X)| ≤
      C * (∫ x in closedBall z r, |SobolevSpace.toLp (hausdorff n X) hX.quadratic φ x| ∂hausdorff n X) * |t-s| := by
  let μ := hausdorff n X
  let Ω := closedBall z r
  obtain ⟨L,hL,htime⟩ := hX.compact_heat_pairing_time_bound hn p ν ρ hρ hρ0 hB hν hδ z hR hdist (r := r)
  obtain ⟨_Lg,A,hbound⟩ := hX.fixed_gauge_local_bounds hn p hK ν ρ hρ hρ0 hB hν z hR hdist hr hδ
  refine ⟨L^2/2,by positivity,?_⟩
  intro φ hφs Bφ hBφ s hs hsN t ht htN
  let Φ := SobolevSpace.toLp μ hX.quadratic φ
  let H := fun k u x => hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k))
    (hε (ι k)) δ hδ z u x
  have hiΦ : IntegrableOn Φ Ω μ :=
    lp_integrableOn_of_finite μ Φ Ω (isCompact_closedBall z r).measure_lt_top.ne
  have hlim (u : ℝ) (hu : u ∈ Ioo δ 1) (huN : u ∉ N) :
      Tendsto (fun k => ∫ x in Ω, Φ x*H k u x ∂μ) atTop
        (𝓝 (∫ x in Ω, Φ x*G u x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |Φ x| * (A:ℝ))
    · intro k
      have hm : Measurable (H k u) := by
        have hmarg : Measurable (fun x : X => (u,x)) := measurable_const.prodMk measurable_id
        have hh := (hX.fixedGaugeScaledPotential_measurable hn p ν ρ hρ hρ0 hB hν
          (F (ι k)) (hF (ι k)) (hε (ι k)) hδ z).comp
          hmarg
        exact hh
      exact hiΦ.aestronglyMeasurable.mul hm.aestronglyMeasurable
    · exact hiΦ.abs.mul_const _
    · intro k
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((hbound (F (ι k)) (hF (ι k)) (ε (ι k)) (hε (ι k)) (hε1 (ι k)) u
          ⟨hu.1.le,hu.2.le⟩).2 x hx) (abs_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      exact ((hconv u hu huN).tendsto_at ⟨x,hx⟩).const_mul (Φ x)
  have hzero := (hε0.comp hι.tendsto_atTop).div_const 2
  have hrhs := ((hzero.mul_const (L * ∫ x, SobolevSpace.minimalSlope μ hX.quadratic φ x ∂μ)).add_const
    (L^2/2 * ∫ x in Ω, |Φ x| ∂μ)).mul_const |t-s|
  have hle := le_of_tendsto_of_tendsto ((hlim t ht htN).sub (hlim s hs hsN)).abs hrhs
    (Eventually.of_forall fun k => htime (F (ι k)) (hF (ι k)) (ε (ι k)) (hε (ι k))
      (hε1 (ι k)) φ hφs Bφ hBφ s ⟨hs.1.le,hs.2.le⟩ t ⟨ht.1.le,ht.2.le⟩)
  simpa only [zero_div,zero_mul,zero_add] using hle

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
