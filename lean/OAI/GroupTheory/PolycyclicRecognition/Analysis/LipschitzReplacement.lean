import OAI.GroupTheory.PolycyclicRecognition.Geometry.NetSmoothing
import Mathlib.SetTheory.Cardinal.Order

namespace OAI

/-! # Lipschitz replacement with all net choices internal -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Construct a uniformly close Lipschitz representative of every map
with the given coarse upper bound. The net and its order are chosen here. -/
theorem exists_lipschitz_replacement_constants
    {X Y : Type*} [Group X] [MetricSpace X] [ProperSpace X]
    [IsIsometricSMul X X] [MetricSpace Y]
    (c : ControlledContraction Y) (p₀ : Y)
    (hpath : ∀ g : X, ∃ γ : ℝ → X, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ L : ℝ≥0, ∃ E : ℝ, 0 ≤ E ∧ ∀ f : X → Y,
      (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
      ∃ f' : C(X, Y), LipschitzWith L f' ∧ ∀ x, dist (f' x) (f x) ≤ E := by
  classical
  obtain ⟨V, hV, hcover⟩ := exists_unit_separated_net (X := X)
  let : LinearOrder V := linearOrderOfSTO WellOrderingRel
  obtain ⟨L, E, hE, hsmooth⟩ := exists_uniform_net_smoothing hV c p₀ hcover hpath hK hC
  refine ⟨L, E, hE, ?_⟩
  intro f hf
  obtain ⟨hLip, hclose⟩ := hsmooth f hf
  exact ⟨⟨netSmoothedMap hV c p₀ f, hLip.continuous⟩, hLip, hclose⟩

end PolycyclicRecognition

end

end OAI
