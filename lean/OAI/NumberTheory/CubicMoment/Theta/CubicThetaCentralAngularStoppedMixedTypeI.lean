import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMixedTypeI
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralTypeIAdapters

namespace OAI

/-! The published-input Type-I replacement for the literal stopped row.
The coefficient bound is derived from the stopped construction, with no
independent-prime representation or cancellation hypothesis on that row. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem angular_stopped_typeI_mixed_actual (ℓ : ℤ)
    {γ : Type*} {V : γ → ℝ → ℂ} (hVw : UniformLogWeights V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B ξ : ℝ} (hB : 1 ≤ B) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
        (w : Eisenstein → γ) (b A u : ℝ),
      2 ≤ b → b ≤ X → 1 ≤ A → 2 ≤ (b/2)*A → B ≤ (b/2)*A →
      b/2 ≤ ((b/2)*A)^(51/100:ℝ) →
      (∀ r ∈ stoppedIntervalSupport ι X (b/2) b e,
        ∀ x : ℝ, B < x → V (w r) x = 0) →
      ‖∑ r ∈ stoppedIntervalSupport ι X (b/2) b e,
        angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected r*
          (typeIMixedGauss r (V (w r)) A-typeIMixedModel r (V (w r)) A)‖ ≤
        K*A^(-1/6:ℝ)*((b/2)*A)^(5/6-1/100:ℝ) := by
  obtain ⟨M,hM,hcoeff⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  obtain ⟨K,hK,hbound⟩ := typeI_mixed_low_actual  hVw hGamma hB hM.le 0 0
  refine ⟨K,hK,?_⟩
  filter_upwards [hcoeff] with X hcoeff
  intro W hW selected e w b A u hb hbX hA hprod hBprod hscale hcut
  apply hbound w (stoppedIntervalSupport ι X (b/2) b e)
    (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected)
    ((b/2)*A) (b/2) A hprod hBprod (by linarith) hA rfl hscale
  · intro r hr
    have hs := stoppedIntervalSupport_spec X (b/2) b e hr
    exact ⟨hs.1,(Finset.mem_filter.mp hr).2.2.2.1.le,by linarith [hs.2.2]⟩
  · exact hcut
  · intro r hr
    simpa only [pow_zero,mul_one] using
      (hcoeff W hW selected u (b/2) b e (by linarith) hbX).1 r hr

end CubicFirstMoment

end

end OAI
