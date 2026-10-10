import OAI.Analysis.IrrationalRotation.Rotation.RotationNonzero
import OAI.Analysis.IrrationalRotation.Rotation.CircleFiberDecay
import OAI.Analysis.IrrationalRotation.Analysis.FieldPowerBounds

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Invariant233.Rotation

theorem weighted_on_vector_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    weighted θ a ξ =ᵐ[circleMeasure]
      fun x => WeightedShift.operator (orbitWeight θ a x) (ξ x) := by
  filter_upwards [
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (representation θ a ξ),
    representation_on_vector_ae θ a ξ] with x hu ha
  change U (representation θ a ξ) x = _
  rw [U, hu, ha]
  rfl

theorem weightedReal_all_rates_norm_decay {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      ‖weightedReal θ f ^ n‖ ≤ Real.exp (-a * n) := by
  apply InvariantProjection.FieldPowerBounds.all_rates_norm_decay
    (weightedReal θ f)
    (fun x => WeightedShift.operator (orbitWeight θ (complexWeight f) x))
    (weighted_on_vector_ae θ (complexWeight f))
  intro a ha
  filter_upwards [InvariantProjection.CircleWeightDecay.all_rates_decay_of_isContinuousCircleWeight
    hθ hf a ha] with n hn
  apply Filter.Eventually.of_forall
  intro x
  exact InvariantProjection.CircleFiberDecay.norm_fiber_power_le θ f
    (fun x => (hf.2.1 x).1) (orbitWeight θ (complexWeight f))
    (fun _ _ => rfl) n (Real.exp_nonneg _) hn x

theorem weightedReal_normQuasinilpotent {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    NormQuasinilpotent (weightedReal θ f) :=
  norm_quasinilpotent_of_exponential_decay _ (weightedReal_all_rates_norm_decay hθ f hf)

theorem weightedReal_ne_zero_of_isContinuousCircleWeight (θ : ℝ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    weightedReal θ f ≠ 0 := by
  intro h
  have hz := (weightedReal_eq_zero_iff θ f).1 h
  obtain ⟨x, hx⟩ := hf.ae_pos.exists
  simp [hz] at hx

theorem weightedReal_spectrum {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    spectrum ℂ (weightedReal θ f) = {0} :=
  spectrum_eq_zero_of_norm_root_tendsto_zero _ (weightedReal_normQuasinilpotent hθ f hf)

end Invariant233.Rotation

end

end OAI
