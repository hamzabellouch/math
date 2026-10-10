import OAI.Analysis.IrrationalRotation.Rotation.CircleFiberDecay
import OAI.Analysis.IrrationalRotation.Analysis.FieldPowerBounds

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace InvariantProjection.CircleFieldDecay

abbrev Hilbert := Lp Invariant233.WeightedShift.Hilbert 2 Invariant233.circleMeasure

theorem all_rates_fiber_decay {θ : ℝ} (hθ : Irrational θ)
    {f : Invariant233.Circle → ℝ} (hf : Invariant233.IsContinuousCircleWeight f)
    (w : Invariant233.Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Invariant233.Circle)) : ℂ)) :
    ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop, ∀ x,
      ‖Invariant233.WeightedShift.operator (w x) ^ n‖ ≤ Real.exp (-a * n) := by
  intro a ha
  filter_upwards [CircleWeightDecay.all_rates_decay_of_isContinuousCircleWeight hθ hf a ha]
    with n hn
  exact CircleFiberDecay.norm_fiber_power_le θ f (fun x => (hf.2.1 x).1)
    w hw n (Real.exp_nonneg _) hn

theorem all_rates_norm_decay {θ : ℝ} (hθ : Irrational θ)
    {f : Invariant233.Circle → ℝ} (hf : Invariant233.IsContinuousCircleWeight f)
    (w : Invariant233.Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Invariant233.Circle)) : ℂ))
    (T : Hilbert →L[ℂ] Hilbert)
    (hT : ∀ ξ : Hilbert,
      ⇑(T ξ) =ᵐ[Invariant233.circleMeasure]
        fun x => Invariant233.WeightedShift.operator (w x) (ξ x)) :
    ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop,
      ‖T ^ n‖ ≤ Real.exp (-a * n) := by
  apply FieldPowerBounds.all_rates_norm_decay T
    (fun x => Invariant233.WeightedShift.operator (w x)) hT
  intro a ha
  filter_upwards [all_rates_fiber_decay hθ hf w hw a ha] with n hn
  exact Filter.Eventually.of_forall hn

theorem norm_quasinilpotent {θ : ℝ} (hθ : Irrational θ)
    {f : Invariant233.Circle → ℝ} (hf : Invariant233.IsContinuousCircleWeight f)
    (w : Invariant233.Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Invariant233.Circle)) : ℂ))
    (T : Hilbert →L[ℂ] Hilbert)
    (hT : ∀ ξ : Hilbert,
      ⇑(T ξ) =ᵐ[Invariant233.circleMeasure]
        fun x => Invariant233.WeightedShift.operator (w x) (ξ x)) :
    Invariant233.NormQuasinilpotent T :=
  Invariant233.norm_quasinilpotent_of_exponential_decay T
    (all_rates_norm_decay hθ hf w hw T hT)

end InvariantProjection.CircleFieldDecay

end

end OAI
