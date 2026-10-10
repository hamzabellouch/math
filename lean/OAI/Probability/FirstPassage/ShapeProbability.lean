import OAI.Probability.FirstPassage.Localization
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
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

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ae_eventually_goodOrigin (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (α : ℝ) (hα : 0 < α) (hlower : ∀ v, α*‖v‖ ≤ μ v)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, GoodOrigin μ α C η δ n (fun e => τ e ω) := by
  filter_upwards [h.ae_positive, ae_uniform_rescaledPassage h μ hμ ht,
    exponential_uniform_shape h μ hμ ht] with ω hp hu hs
  have hb := uniform_rescaled_ball_bound _ μ hμ hu C hC η hη
  have he' : ∀ᶠ n : ℕ in atTop, ∀ z : Vertex, δ*n/3 ≤ ‖latticeEmbed z‖ →
      α*δ*n/6 ≤ passageTime (fun e => τ e ω) 0 z :=
    tendsto_natCast_atTop_atTop.eventually (hs.eventually_escape _ μ α δ hα hδ hlower)
  filter_upwards [hb,he'] with n hn he
  exact ⟨fun e => (hp e).le, hn, he⟩

theorem goodOrigin_failure_tendsto_zero (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (α : ℝ) (hα : 0 < α) (hlower : ∀ v, α*‖v‖ ≤ μ v)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n => P.real {ω | ¬GoodOrigin μ α C η δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by
  let _ := h.probability
  apply measureReal_tendsto_zero_of_ae_eventually_notMem
  · intro n
    exact ((measurableSet_goodOrigin μ α C η δ n).preimage
      (Measurable.of_eval h.measurable)).compl
  · simpa only [mem_ofPred_eq, not_not] using
      ae_eventually_goodOrigin h μ hμ ht α hα hlower C hC η δ hη hδ

theorem translated_goodOrigin_failure_probability (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ) (p : Vertex) :
    P {ω | ¬GoodOrigin μ α C η δ n (fun e => τ (shiftEdge p e) ω)} =
      P {ω | ¬GoodOrigin μ α C η δ n (fun e => τ e ω)} :=
  translated_event_probability h p _ (measurableSet_goodOrigin μ α C η δ n).compl

end PlanarFPP

end OAI
