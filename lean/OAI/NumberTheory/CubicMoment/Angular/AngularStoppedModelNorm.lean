import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedModelNorm
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCharacterRows

namespace OAI

/-! The model polynomial of a bounded stopped row has the expected
b^(5/6) size, directly from its literal norm support. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_model_norm (ℓ : ℤ) {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein) (b u v : ℝ),
      0 < b → b ≤ X →
      ‖dispersionModel (stoppedIntervalSupport ι X (b/2) b e)
        (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected) v‖ ≤ K*b^(5/6:ℝ) := by
  obtain ⟨M,hM,hbound⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  refine ⟨18*(2:ℝ)^(1/6:ℝ)*M,by positivity,?_⟩
  filter_upwards [hbound] with X hbound
  intro W hW selected e b u v hb hbX
  apply bounded_annular_model_norm _ _ hb hM.le
  · intro a ha
    have hs := stoppedIntervalSupport_spec X (b/2) b e ha
    exact ⟨hs.1,(Finset.mem_filter.mp ha).2.2.2.1.le,hs.2.2⟩
  · exact (hbound W hW selected u (b/2) b e hb.le hbX).1

end CubicFirstMoment

end

end OAI
