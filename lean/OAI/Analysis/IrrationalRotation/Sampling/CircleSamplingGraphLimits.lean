import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingGraph
import OAI.Analysis.IrrationalRotation.Analysis.GraphMeasureConvergence
import OAI.Analysis.IrrationalRotation.Analysis.L2UniformAbsoluteContinuity
import OAI.Analysis.IrrationalRotation.Sampling.CirclePhaseTails

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Invariant233.CircleParameterData

def circleFiniteBase : FiniteMeasure Circle :=
  ⟨circleMeasure, by unfold circleMeasure; infer_instance⟩

instance circleFiniteBase_probability : IsProbabilityMeasure (circleFiniteBase : Measure Circle) := by
  constructor
  change volume (Set.univ : Set Circle) = 1
  exact UnitAddCircle.measure_univ

def samplingGraphFinite (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (hm : 0 < p.m j) : FiniteMeasure (Circle × Circle) :=
  ⟨p.samplingGraphAverage θ j r, p.samplingGraphAverage_finite θ j r hm⟩

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws

open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem samplingAverage_error_tendsto_zero
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) (endpoint : Bool) :
    Tendsto (fun n => eLpNorm (fun x => p.samplingAverage θ (j n) (r n) endpoint x - 1)
      2 circleMeasure) atTop (𝓝 0) := by
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_one_div_atTop_nhds_zero_nat.comp hjt)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => ENNReal.ofReal (1 / (j n : ℝ))) atTop (𝓝 0) from by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using hlim)
    (fun _ => bot_le)
    (fun n => (hp.sampling_L2 (j n) (hj n) (r n) (hr n) endpoint).le)

theorem tendsto_samplingGraph_first_marginal
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) :
    Tendsto (fun n => (p.samplingGraphFinite θ (j n) (r n) (hp.m_pos _ (hj n))).map Prod.fst)
      atTop (𝓝 circleFiniteBase) := by
  apply GraphMeasureConvergence.tendsto_of_density_L2 circleFiniteBase _
    (fun n => p.samplingAverage θ (j n) (r n) false)
  · intro n
    exact p.memLp_samplingAverage θ (j n) (r n) false (hp.m_pos _ (hj n)) 2
  · intro n
    exact Eventually.of_forall fun x =>
      (p.samplingAverage_bounds θ (j n) (r n) false (hp.m_pos _ (hj n)) x).1
  · intro n
    exact p.samplingGraphAverage_first_marginal θ (j n) (r n) (hp.m_pos _ (hj n))
  · exact hp.samplingAverage_error_tendsto_zero j r hj hr hjt false

theorem tendsto_samplingGraph_second_marginal
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) :
    Tendsto (fun n => (p.samplingGraphFinite θ (j n) (r n) (hp.m_pos _ (hj n))).map Prod.snd)
      atTop (𝓝 circleFiniteBase) := by
  apply GraphMeasureConvergence.tendsto_of_density_L2 circleFiniteBase _
    (fun n => p.samplingAverage θ (j n) (r n) true)
  · intro n
    exact p.memLp_samplingAverage θ (j n) (r n) true (hp.m_pos _ (hj n)) 2
  · intro n
    exact Eventually.of_forall fun x =>
      (p.samplingAverage_bounds θ (j n) (r n) true (hp.m_pos _ (hj n)) x).1
  · intro n
    exact p.samplingGraphAverage_second_marginal θ (j n) (r n) (hp.m_pos _ (hj n))
  · exact hp.samplingAverage_error_tendsto_zero j r hj hr hjt true

theorem samplingGraph_marginals_uniformlyAbsolutelyContinuous
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1))) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (p.samplingGraphAverage θ (j n) (r n)).map Prod.fst) ∧
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (p.samplingGraphAverage θ (j n) (r n)).map Prod.snd) := by
  let : IsFiniteMeasure circleMeasure := by unfold circleMeasure; infer_instance
  have hden (endpoint : Bool) : UniformlyAbsolutelyContinuous circleMeasure
      (fun n => circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingAverage θ (j n) (r n) endpoint x))) := by
    apply EndpointLoss.uniformlyAbsolutelyContinuous_withDensity circleMeasure
      (fun n => p.samplingAverage θ (j n) (r n) endpoint)
      (fun n => p.memLp_samplingAverage θ (j n) (r n) endpoint (hp.m_pos _ (hj n)) 2)
      (fun n => Eventually.of_forall fun x =>
        (p.samplingAverage_bounds θ (j n) (r n) endpoint (hp.m_pos _ (hj n)) x).1) 2
    intro n
    rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm
      (p.memLp_samplingAverage θ (j n) (r n) endpoint (hp.m_pos _ (hj n)) 2)]
    have h := ENNReal.toReal_mono (by norm_num : (2 : ENNReal) ≠ ∞)
      (hp.samplingAverage_eLpNorm_le_two (j n) (hj n) (r n) (hr n) endpoint)
    simpa only [ENNReal.toReal_ofNat] using h
  constructor
  · convert hden false using 1
    funext n
    exact p.samplingGraphAverage_first_marginal θ (j n) (r n) (hp.m_pos _ (hj n))
  · convert hden true using 1
    funext n
    exact p.samplingGraphAverage_second_marginal θ (j n) (r n) (hp.m_pos _ (hj n))

theorem ell_nonneg_and_le (j : ℕ) : 0 ≤ p.ell j ∧
    p.ell j ≤ 1 / ((j + 1 : ℕ) : ℝ)^2 := by
  have hq : (1 : ℝ) ≤ p.q (p.blockEnd (j - 1)) := by
    exact_mod_cast hp.q_pos (p.blockEnd (j - 1))
  have ha : 0 ≤ (p.blockEnd (j - 1) : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ)^2 := by positivity
  have hprod : 1 ≤ (1 + (p.blockEnd (j - 1) : ℝ)) *
      (p.q (p.blockEnd (j - 1)) : ℝ) :=
    one_le_mul_of_one_le_of_one_le (by linarith) hq
  unfold ell
  constructor
  · positivity
  · apply one_div_le_one_div_of_le hj
    nlinarith

theorem tendsto_ell_zero : Tendsto p.ell atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
  have hsq : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div_pow, zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  exact squeeze_zero (fun n => (hp.ell_nonneg_and_le n).1)
    (fun n => (hp.ell_nonneg_and_le n).2) hsq

theorem samplingGraphAverage_ae_dist_lt
    (j : ℕ) (hj : 1 ≤ j) (r : ℕ)
    (hr : r < p.q (p.blockEnd (j - 1))) (t : Circle)
    (hshift : (p.shift j r : Circle) = t) :
    ∀ᵐ z ∂p.samplingGraphAverage θ j r, dist z.2 (z.1 + t) < p.ell j := by
  filter_upwards [p.samplingGraphAverage_ae_graph θ j r] with z hz
  obtain ⟨k, hk, heq⟩ := hz
  have hphase := (hp.samples_phase j hj r hr k hk).2
  rw [heq]
  change dist (z.1 + (((k : ℝ) * θ : ℝ) : Circle)) (z.1 + t) < p.ell j
  rw [dist_add_left, ← hshift, dist_eq_norm, ← AddCircle.coe_sub]
  calc
    ‖(((k : ℝ) * θ - p.shift j r : ℝ) : Circle)‖ =
        ‖((Int.fract ((k : ℝ) * θ - p.shift j r) : ℝ) : Circle)‖ := by
      rw [AddCircle.coe_fract]
    _ ≤ ‖Int.fract ((k : ℝ) * θ - p.shift j r)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = Int.fract ((k : ℝ) * θ - p.shift j r) :=
      Real.norm_of_nonneg (Int.fract_nonneg _)
    _ < p.ell j := hphase

theorem tendsto_samplingGraph_translation
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) (t : Circle)
    (hshift : ∀ n, (p.shift (j n) (r n) : Circle) = t) :
    Tendsto (fun n => p.samplingGraphFinite θ (j n) (r n) (hp.m_pos _ (hj n)))
      atTop (𝓝 (circleFiniteBase.map (fun x => (x, x + t)))) := by
  apply GraphMeasureConvergence.tendsto_graph_of_first_marginal _ circleFiniteBase
    (fun x => x + t) (continuous_id.add continuous_const)
    (hp.tendsto_samplingGraph_first_marginal j r hj hr hjt)
  intro δ hδ
  filter_upwards [(hp.tendsto_ell_zero.comp hjt).eventually_lt_const hδ] with n hn
  exact (hp.samplingGraphAverage_ae_dist_lt (j n) (hj n) (r n) (hr n) t (hshift n)).mono
    (fun _ hz => hz.trans hn)

theorem tendsto_samplingGraph_translation_trimmed
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) (t : Circle)
    (hshift : ∀ n, (p.shift (j n) (r n) : Circle) = t)
    (s : ℕ → Set Circle) (hs : ∀ n, MeasurableSet (s n))
    (hbase : Tendsto (fun n => circleMeasure.real (s n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (p.samplingGraphFinite θ (j n) (r n) (hp.m_pos _ (hj n))).restrict
      (Prod.fst ⁻¹' s n)) atTop (𝓝 (circleFiniteBase.map (fun x => (x, x + t)))) := by
  apply GraphMeasureConvergence.tendsto_trimmed_graph_of_uniform_first_marginal
    _ circleFiniteBase (fun x => x + t) (continuous_id.add continuous_const)
    (hp.tendsto_samplingGraph_first_marginal j r hj hr hjt) _
    (hp.samplingGraph_marginals_uniformlyAbsolutelyContinuous j r hj hr).1 s hs hbase
  intro δ hδ
  filter_upwards [(hp.tendsto_ell_zero.comp hjt).eventually_lt_const hδ] with n hn
  exact (hp.samplingGraphAverage_ae_dist_lt (j n) (hj n) (r n) (hr n) t (hshift n)).mono
    (fun _ hz => hz.trans hn)

end Invariant233.CircleParameterLaws

end

end OAI
