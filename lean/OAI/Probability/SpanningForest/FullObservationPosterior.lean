import OAI.Probability.SpanningForest.PosteriorIndependentExtension
import OAI.Probability.SpanningForest.BrownianBridge

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336.Observation

theorem condExp_brownian_history_eq_endpoint
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hBm : ∀ s, Measurable (B s)) (X : Ω → ℝ) (hX : Measurable X)
    (hXB : IndepFun X (fun ω s => B s ω) P)
    (t : ℝ≥0) (ht : t ≠ 0)
    (g : ℝ → ℝ) (hg : Measurable g) (hgi : Integrable (fun ω => g (X ω)) P) :
    P[fun ω => g (X ω) |
      MeasurableSpace.comap (fun ω (s : Set.Iic t) =>
        (s : ℝ) * X ω + B s ω) inferInstance] =ᵐ[P]
      P[fun ω => g (X ω) |
        MeasurableSpace.comap (fun ω => (t : ℝ) * X ω + B t ω) inferInstance] := by
  rw [BrownianBridge.history_comap_eq_endpoint_residual
    (fun r ω => (r : ℝ) * X ω + B r ω) t]
  simp_rw [BrownianBridge.residual_add_linear X t _ ht]
  have hbridge : Measurable
      (fun ω (s : Set.Iic t) => BrownianBridge.residual B t s ω) := by
    apply Measurable.of_eval
    intro s
    exact (hBm s).sub ((hBm t).const_mul _)
  exact condExp_pair_of_indep P X (fun ω => (t : ℝ) * X ω + B t ω)
    (fun ω (s : Set.Iic t) => BrownianBridge.residual B t s ω)
    hX ((hX.const_mul _).add (hBm t)) hbridge g hg hgi
    (BrownianBridge.indepFun_residual_hidden_endpoint hB hBm hX hXB t ht).symm

end Problem336.Observation

end

end OAI
