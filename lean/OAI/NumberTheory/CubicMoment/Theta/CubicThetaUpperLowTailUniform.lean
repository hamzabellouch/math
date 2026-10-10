import OAI.NumberTheory.CubicMoment.Angular.AngularUpperLowTailUniform
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUpperNoStopNegligible

namespace OAI

/-! Actual angular tail estimate, with the theta transform constructed. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_upperLowTail_isLittleO_uniform_proved (hℓ : ℓ ≠ 0) (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/12 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ < κ/2 →
      ∀ m : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ κ/4 ∧ ∀ H T : ℝ → ℝ,
        (∀ᶠ X : ℝ in atTop, Real.log X ≤ T X) →
        (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
        (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+η/2)) →
        (fun X => angular_upperLowTail ℓ m κ ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hstop⟩ := angular_upperStoppedFilteredTail_isLittleO_uniform ℓ hpnt hMV hC hHuxley
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle
  have hκsmall : κ < 1/12 := hκle.trans_lt hκ₀small
  have hstop := hstop κ hκ hκle
  intro ξ _hξ hξsmall m
  let η := κ/8
  let ε := (κ/2-ξ)/2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηκ : η ≤ κ/4 := by dsimp [η]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < κ/2 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨ρ,hρ,hρ₂,hsmall,hno⟩ := angular_upperNoStopTail_isLittleO_proved ℓ hℓ m hpnt hMV hC hκ hκsmall hη hηκ hcap
  refine ⟨η,hη,hηκ,?_⟩
  intro H T hT hH hHX
  have hsetup : ∀ᶠ X : ℝ in atTop,
      1 ≤ H X ∧ H X ≤ X^(1/6+η/2) ∧ Real.log X ≤ T X := by
    filter_upwards [hT,hH,hHX] with X ht hh hx
    exact ⟨hh,hx,ht⟩
  have hHhalf : ∀ᶠ X : ℝ in atTop, H X ≤ X^(1/2:ℝ) := by
    filter_upwards [hHX,eventually_ge_atTop (1:ℝ)] with X hx hX
    exact hx.trans (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [η]; linarith))
  have hsum := (hno ξ H T hsetup).add
    (hstop ρ ξ ε hρ hρ₂ hε.le hsmall hgap m H T hT hH hHhalf)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [angular_upperLowTail_stopping ℓ m ξ hκ] with X hid
  exact (hid ρ hρ hρ₂ (H X) (T X)).symm


end CubicFirstMoment

end

end OAI
