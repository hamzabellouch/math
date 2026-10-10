import OAI.Probability.GammaPassage.Environment
import OAI.Probability.GammaPassage.ScalingLaw
import OAI.Probability.GammaPassage.FirstMoment
import OAI.Probability.GammaPassage.Scaling

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate a : ℝ}

/-- Scaling every edge weight by `a > 0` divides the Gamma rate by `a` and preserves independence. -/
theorem GammaEnvironment.scale
    (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (ha : 0 < a) :
    GammaEnvironment shape (rate / a) P (fun e ω => a * τ e ω) where
  probability := h.probability
  measurable e := measurable_const.mul (h.measurable e)
  independent := h.independent.comp (fun _ (x : ℝ) => a * x)
    (fun _ => measurable_const.mul measurable_id)
  marginal e := by
    have hm : Measurable (fun x : ℝ => a * x) :=
      measurable_const.mul measurable_id
    change Measure.map ((fun x : ℝ => a * x) ∘ τ e) P = _
    rw [← Measure.map_map hm (h.measurable e), h.marginal e]
    exact map_mul_gammaMeasure hshape hrate ha

theorem GammaEnvironment.ae_positive_edges
    (h : GammaEnvironment shape rate P τ) :
    ∀ᵐ ω ∂P, ∀ e, 0 < τ e ω := by
  rw [ae_all_iff]
  intro e
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact gamma_ae_pos shape rate
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

/-- Scaling the environment transports the almost-sure limit for each fixed real direction. -/
theorem GammaEnvironment.scale_with_timeConstant
    (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (ha : 0 < a)
    {μ : PlanarFPP.Plane → ℝ} (hμ : PlanarFPP.IsTimeConstant P τ μ) :
    GammaEnvironment shape (rate / a) P (fun e ω => a * τ e ω) ∧
      PlanarFPP.IsTimeConstant P (fun e ω => a * τ e ω) (fun v => a * μ v) := by
  refine ⟨h.scale hshape hrate ha, ?_⟩
  apply isTimeConstant_scale (μ := μ) ?_ hμ a ha
  exact h.ae_positive_edges.mono (fun ω hω e => (hω e).le)

end GammaFPP

end OAI
