import OAI.NumberTheory.DukePrimeDegree.Dynamics.FlowSmoothedL2
import OAI.NumberTheory.DukePrimeDegree.Dynamics.BoundedGenericSet
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-!
# Bounded observable smoothing for an ergodic real flow

Unit smoothing is measurable, bounded, and preserves the integral.
Its discrete averages have an actual L1 limit under flow ergodicity.
Together with the maximal estimate this gives fixed large-measure sets
that control every sufficiently long integer flow window.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [MulAction (Multiplicative ℝ) X] [ContinuousSMul (Multiplicative ℝ) X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuous_flow_observable (f : X →ᵇ ℝ) :
    Continuous (fun p : ℝ × X => f (realActionTime p.1 p.2)) := by
  unfold realActionTime
  fun_prop

lemma measurable_unitFlowSmooth (f : X →ᵇ ℝ) :
    Measurable (unitFlowSmooth realActionTime f) := by
  have hj : StronglyMeasurable (fun p : X × ℝ => f (realActionTime p.2 p.1)) :=
    ((continuous_flow_observable f).comp continuous_swap).stronglyMeasurable
  have hm := hj.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
  unfold unitFlowSmooth
  simpa only [intervalIntegral.integral_of_le zero_le_one] using hm.measurable

omit [MeasurableSpace X] [BorelSpace X] [ContinuousSMul (Multiplicative ℝ) X] in
lemma unitFlowSmooth_abs_le (f : X →ᵇ ℝ) (x : X) :
    |unitFlowSmooth realActionTime f x| ≤ ‖f‖ := by
  simpa only [unitFlowSmooth, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => f (realActionTime t x))
      (a := 0) (b := 1) (C := ‖f‖)
      (fun t _ => f.norm_coe_le_norm (realActionTime t x)))

lemma memLp_unitFlowSmooth (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ ℝ) :
    MemLp (unitFlowSmooth realActionTime f) 2 μ :=
  MemLp.of_bound (measurable_unitFlowSmooth f).aestronglyMeasurable ‖f‖
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using unitFlowSmooth_abs_le f x)

lemma unitFlowSmooth_integral_eq (μ : Measure X) [IsFiniteMeasure μ]
    [SMulInvariantMeasure (Multiplicative ℝ) X μ] (f : X →ᵇ ℝ) :
    (∫ x, unitFlowSmooth realActionTime f x ∂μ) = ∫ x, f x ∂μ := by
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
    rw [uIoc_of_le zero_le_one]
    infer_instance
  have hi : Integrable (fun p : ℝ × X => f (realActionTime p.1 p.2))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound
      (continuous_flow_observable f).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun p => f.norm_coe_le_norm (realActionTime p.1 p.2)))
  have he (t : ℝ) : (∫ x, f (realActionTime t x) ∂μ) = ∫ x, f x ∂μ := by
    have hp : MeasurePreserving (realActionTime t) μ μ :=
      measurePreserving_smul (Multiplicative.ofAdd t) μ
    have hmap := integral_map hp.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x => f x) (μ.map (realActionTime t)) from
        by rw [hp.map_eq]; exact f.continuous.aestronglyMeasurable)
    rw [hp.map_eq] at hmap
    exact hmap.symm
  unfold unitFlowSmooth
  rw [← intervalIntegral_integral_swap hi]
  simp_rw [he]
  simp

/-- The genuine continuous-flow windows converge in L1 at integer
lengths. Full-flow ergodicity is the only ergodicity hypothesis. -/
theorem L1_integer_flow_windows_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) X μ]
    (f : X →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ x,
      |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (realActionTime t x)) -
        ∫ y, f y ∂μ| ∂μ) atTop (𝓝 0) := by
  let g : X → ℝ := unitFlowSmooth realActionTime f
  have hg := memLp_unitFlowSmooth μ f
  have ht : ∀ x a b, IntervalIntegrable (fun t => f (realActionTime t x)) volume a b :=
    fun x a b => ((continuous_flow_observable f).comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hL2 := L2_unit_smoothed_real_action_tendsto_integral μ f ‖f‖ (norm_nonneg f)
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) ht hg
  have hL1 := L1_tendsto_of_L2_tendsto_constant μ _ _ hL2
  change Tendsto (fun N : ℕ => ∫ x,
    |(birkhoffAverage ℝ (Lp.compMeasurePreserving (realActionTime 1)
      (measurePreserving_smul (Multiplicative.ofAdd 1) μ)) id N (hg.toLp g)) x -
      ∫ y, g y ∂μ| ∂μ) atTop (𝓝 0) at hL1
  have he (N : ℕ) :
      (∫ x, |(birkhoffAverage ℝ
        (Lp.compMeasurePreserving (realActionTime 1)
          (measurePreserving_smul (Multiplicative.ofAdd 1) μ)) id N (hg.toLp g)) x -
          ∫ y, g y ∂μ| ∂μ) =
      ∫ x, |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (realActionTime t x)) -
          ∫ y, f y ∂μ| ∂μ := by
    apply integral_congr_ae
    have hrep := (Lp_orbit_average_ae μ (realActionTime 1)
      (measurePreserving_smul (Multiplicative.ofAdd 1) μ) (hg.toLp g) N).trans
      (orbit_average_congr_ae μ (realActionTime 1)
        (measurePreserving_smul (Multiplicative.ofAdd 1) μ) hg.coeFn_toLp N)
    filter_upwards [hrep] with x hx
    rw [hx, birkhoffAverage_unitFlowSmooth realActionTime f realActionTime_zero
      realActionTime_add ht, unitFlowSmooth_integral_eq μ f]
  simpa only [he] using hL1

/-- A fixed large-measure set works for all sufficiently large integer
flow windows, including a window length selected from a pair of points. -/
theorem exists_uniform_integer_flow_generic_set
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) X μ]
    (f : X →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set X, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ N ≥ N₀,
        |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (realActionTime t x)) -
          ∫ y, f y ∂μ| ≤ ε := by
  let g : X → ℝ := unitFlowSmooth realActionTime f
  have ht : ∀ x a b, IntervalIntegrable (fun t => f (realActionTime t x)) volume a b :=
    fun x a b => ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hmean : Tendsto (fun N : ℕ => ∫ x,
      |birkhoffAverage ℝ (realActionTime 1) g N x - ∫ y, f y ∂μ| ∂μ)
      atTop (𝓝 0) := by
    simpa only [g, birkhoffAverage_unitFlowSmooth realActionTime f
      realActionTime_zero realActionTime_add ht] using L1_integer_flow_windows_tendsto_integral μ f
  obtain ⟨G, hG, hGμ, N₀, hN₀⟩ := exists_uniform_generic_set_of_L1_convergence μ
    (realActionTime 1) (measurePreserving_smul (Multiplicative.ofAdd 1) μ)
    g (measurable_unitFlowSmooth f)
    (memLp_one_iff_integrable.mp ((memLp_unitFlowSmooth μ f).mono_exponent (by norm_num)))
    ‖f‖ (norm_nonneg f) (unitFlowSmooth_abs_le f) (∫ y, f y ∂μ) hmean ε δ hε hδ
  refine ⟨G, hG, hGμ, N₀, ?_⟩
  intro x hx N hN
  simpa only [g, birkhoffAverage_unitFlowSmooth realActionTime f
    realActionTime_zero realActionTime_add ht] using hN₀ x hx N hN

end DukePrimeDegree

end

end OAI
