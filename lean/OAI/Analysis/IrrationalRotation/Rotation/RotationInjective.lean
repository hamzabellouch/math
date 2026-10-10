import OAI.Analysis.IrrationalRotation.Spectral.RotationQuasinilpotent

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.Rotation

theorem representation_operator_injective_of_orbit_nonzero
    (θ : ℝ) (a : C(Circle, ℂ))
    (ha : ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, a (action θ k x) ≠ 0) :
    Function.Injective (representation θ a) := by
  intro ξ η h
  apply Lp.ext
  filter_upwards [representation_on_vector_ae θ a ξ,
    representation_on_vector_ae θ a η, ha] with x hξ hη hax
  apply lp.ext
  funext k
  have hx : WeightedShift.diagonal (orbitWeight θ a x) (ξ x) =
      WeightedShift.diagonal (orbitWeight θ a x) (η x) := by
    rw [← hξ, ← hη, h]
  have hk := congrArg (fun v : Fiber => v k) hx
  change a (action θ k x) * ξ x k = a (action θ k x) * η x k at hk
  exact mul_left_cancel₀ (hax k) hk

theorem orbitWeight_nonzero_ae (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, complexWeight f (action θ k x) ≠ 0 := by
  apply ae_all_iff.mpr
  intro k
  have hne : ∀ᵐ x ∂circleMeasure, x ≠ -(k • (θ : Circle)) := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton]
      using (circleMeasure_singleton (-(k • (θ : Circle))))
  filter_upwards [hne] with x hx
  intro hzero
  have hreal : f (action θ k x) = 0 := by simpa [complexWeight] using hzero
  have horbit := (hf.2.2.1 (action θ k x)).mp hreal
  apply hx
  change x + k • (θ : Circle) = 0 at horbit
  exact eq_neg_of_add_eq_zero_left horbit

theorem representation_real_injective (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    Function.Injective (representation θ (complexWeight f)) :=
  representation_operator_injective_of_orbit_nonzero θ (complexWeight f)
    (orbitWeight_nonzero_ae θ f hf)

theorem weightedReal_injective (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    Function.Injective (weightedReal θ f) :=
  fiberShift_operator_injective.comp (representation_real_injective θ f hf)

theorem representation_real_ker_eq_bot (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    (representation θ (complexWeight f)).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (representation_real_injective θ f hf)

end Invariant233.Rotation

end

end OAI
