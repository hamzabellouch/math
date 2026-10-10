import OAI.Geometry.RCD.Heat.ExponentialIntegralBounds
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! # The compact Laplace limit on the actual support of a probability law

No full-support hypothesis is imposed on the surrounding compact space.
The maximum is taken on the measure support, which is nonempty and conull.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem compact_laplace_limit (F : ℕ → X → ℝ) (f : X → ℝ)
    (hF : ∀ k, Continuous (F k)) (hf : Continuous f) (hlim : TendstoUniformly F f atTop)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ x ∈ μ.support, (∀ y ∈ μ.support, f y ≤ f x) ∧
      Tendsto (fun k => ε k*Real.log (∫ y, Real.exp (F k y/ε k) ∂μ)) atTop (𝓝 (f x)) := by
  obtain ⟨x,hx,hmax⟩ := μ.isClosed_support.isCompact.exists_isMaxOn
    (μ.nonempty_support (IsProbabilityMeasure.ne_zero μ)) hf.continuousOn
  refine ⟨x,hx,hmax,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let d := η/4
  have hd : 0 < d := by dsimp only [d]; positivity
  let U := {y : X | f x-d < f y}
  have hU : IsOpen U := isOpen_lt continuous_const hf
  have hxU : x ∈ U := by change f x-d < f x; linarith
  have hm : 0 < μ.real U := ENNReal.toReal_pos
    ((Measure.mem_support_iff_forall x).mp hx U (hU.mem_nhds hxU)).ne' (measure_ne_top μ U)
  have hlog : Tendsto (fun k => ε k*Real.log (μ.real U)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hε0.mul_const (Real.log (μ.real U))
  filter_upwards [(Metric.tendstoUniformly_iff.mp hlim) d hd,
    hlog.eventually (lt_mem_nhds (by linarith : -d < (0:ℝ)))] with k hk hlogk
  have hi : Integrable (fun y => Real.exp (F k y/ε k)) μ :=
    (Real.continuous_exp.comp ((hF k).div_const (ε k))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlo : ∀ᵐ y ∂μ.restrict U, f x-2*d ≤ F k y := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    have hh := hk y
    rw [Real.dist_eq] at hh
    have hdiff := (abs_lt.mp hh).2
    change f x-d < f y at hy
    linarith
  have hup : ∀ᵐ y ∂μ, F k y ≤ f x+d := by
    filter_upwards [μ.support_mem_ae] with y hy
    have hh := hk y
    rw [Real.dist_eq] at hh
    have hdiff := (abs_lt.mp hh).1
    have hm := hmax hy
    change f y ≤ f x at hm
    linarith
  obtain ⟨_hp,hl,hu⟩ := exponential_integral_log_bounds μ (hε k) hm hi hlo hup
  rw [Real.dist_eq]
  apply abs_lt.mpr
  dsimp only [d] at hl hu hlogk
  constructor <;> linarith

end RegularPointCoordinates

end

end OAI
