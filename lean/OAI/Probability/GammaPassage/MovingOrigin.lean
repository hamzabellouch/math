import OAI.Probability.GammaPassage.OriginEscapeLower
import OAI.Probability.GammaPassage.Stationarity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem measureReal_tendsto_zero_of_ae_eventually_notMem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (he : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∉ A n) :
    Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
  classical
  let F : ℕ → Ω → ℝ := fun n => (A n).indicator (fun _ => 1)
  have hm (n) : Measurable (F n) := measurable_const.indicator (hA n)
  have ht : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
    filter_upwards [he] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    simp [F, hn]
  have hi := tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable) ht
  have hp := (tendstoInMeasure_iff_measureReal_norm.mp hi) (1/2) (by norm_num)
  have heq (n : ℕ) : {ω | (1/2 : ℝ) ≤ ‖F n ω-0‖} = A n := by
    ext ω
    by_cases hω : ω ∈ A n <;> norm_num [F, hω]
  simpa only [heq] using hp

def GoodOrigin (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ)
    (w : Edge → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧
  (∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
    |passageTime w 0 z-μ (latticeEmbed z)| ≤ η*n) ∧
  (∀ z : Vertex, δ*n/3 ≤ ‖latticeEmbed z‖ → α*δ*n/6 ≤ passageTime w 0 z)

theorem measurableSet_goodOrigin (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ) :
    MeasurableSet {w | GoodOrigin μ α C η δ n w} := by
  unfold GoodOrigin
  simp only [ofPred_and, ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun e => ?_) ?_
  · exact measurableSet_le measurable_const (measurable_pi_apply e)
  refine MeasurableSet.inter (MeasurableSet.iInter fun z => ?_)
    (MeasurableSet.iInter fun z => ?_)
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (continuous_abs.measurable.comp ((measurable_passageTime measurable_pi_apply 0 z).sub_const _))
      measurable_const
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le measurable_const (measurable_passageTime measurable_pi_apply 0 z)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {ν : Measure ℝ} {shape rate : ℝ}

/-- Equality in law holds separately at each scale; a may vary arbitrarily. -/
theorem moving_origin_failure_tendsto
    (h : IidEnvironment ν P τ) (A : ℕ → Set (Edge → ℝ))
    (hA : ∀ n, MeasurableSet (A n)) (a : ℕ → Vertex)
    (ht : Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∉ A n}) atTop (𝓝 0)) :
    Tendsto (fun n => P.real {ω | (fun e => τ (shiftEdge (a n) e) ω) ∉ A n})
      atTop (𝓝 0) := by
  have he (n : ℕ) :
      P.real {ω | (fun e => τ (shiftEdge (a n) e) ω) ∉ A n} =
        P.real {ω | (fun e => τ e ω) ∉ A n} :=
    congrArg ENNReal.toReal (h.translated_event_probability (a n) (A n)ᶜ (hA n).compl)
  simpa only [he] using ht

/-- Actual origin good tests, with the norm lower coefficient already derived. -/
theorem ae_eventually_gamma_goodOrigin
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      GoodOrigin (gammaMeanNorm h hs hr) (cheapSlope shape rate) C η δ n
        (fun e => τ e ω) := by
  filter_upwards [h.ae_positive, h.ae_uniform_inside_ball hs hr,
    h.ae_eventually_origin_escape hs hr δ hδ] with ω hp hb he
  have hn := tendsto_natCast_atTop_atTop.eventually he
  filter_upwards [hb C hC η hη, hn] with n hb he
  exact ⟨fun e => (hp e).le, hb, he⟩

/-- GoodOrigin failures vanish even for deterministic origins chosen anew at
each scale. Endpoint geometry is not part of this probability statement. -/
theorem gamma_moving_goodOrigin_failure_tendsto
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (a : ℕ → Vertex) :
    Tendsto (fun n => P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a n) e) ω)})
      atTop (𝓝 0) := by
  let := h.probability
  apply moving_origin_failure_tendsto h
    (fun n => {w | GoodOrigin (gammaMeanNorm h hs hr) (cheapSlope shape rate) C η δ n w})
    (fun n => measurableSet_goodOrigin _ _ _ _ _ n) a
  apply measureReal_tendsto_zero_of_ae_eventually_notMem
  · intro n
    exact ((measurableSet_goodOrigin _ _ _ _ _ n).preimage
      (Measurable.of_eval h.measurable)).compl
  · simpa only [mem_ofPred_eq, not_not] using
      ae_eventually_gamma_goodOrigin h hs hr C hC η δ hη hδ

end GammaFPP.IntervalTravelBridge

end OAI
