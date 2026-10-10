import OAI.NumberTheory.CubicMoment.Angular.AngularUpperStoppedSuffix
import OAI.NumberTheory.CubicMoment.Angular.AngularUpperNoStopNegligible

namespace OAI

/-! The full low distinguished-scale branch at upper heights is negligible.
The single stopping identity is applied before either analytic bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_upperLowArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(1/3-2*κ) then
          scaleFirstTailScaleRow i ℓ ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def angular_upperLowTail (m : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, angular_upperLowArity ℓ i κ ξ H T X

lemma angular_upperLowArity_stopping (i : ℕ) (ξ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ H T : ℝ,
      angular_upperLowArity ℓ i κ ξ H T X = angular_upperNoStopArity ℓ i κ ρ ξ H T X+
        angular_upperStoppedFilteredArity ℓ i κ ρ ξ H T X := by
  filter_upwards [scaleFirstTailScaleRow_upper_stopping i ξ hκ] with X hrow
  intro ρ hρ hρ₂ H T
  unfold angular_upperLowArity angular_upperNoStopArity angular_upperStoppedFilteredArity angular_upperStoppedWindow
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : X^(1/100:ℝ) < T*(3/2:ℝ)^s
  · simp only [hs,ite_true]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : distinguishedScaleLength d < X^(1/3-2*κ)
    · simp only [hd,ite_true]
      exact hrow ρ hρ hρ₂ ℓ H (T*(3/2:ℝ)^s) d hd
    · simp only [hd,ite_false,zero_add]
  · simp only [hs,ite_false,zero_add]

lemma angular_upperLowTail_stopping (m : ℕ) (ξ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ H T : ℝ,
      angular_upperLowTail ℓ m κ ξ H T X = angular_upperNoStopTail ℓ m κ ρ ξ H T X+
        ∑ i ∈ Finset.range m, angular_upperStoppedFilteredArity ℓ i κ ρ ξ H T X := by
  have hall : ∀ᶠ X : ℝ in atTop, ∀ i ∈ Finset.range m,
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ H T : ℝ,
      angular_upperLowArity ℓ i κ ξ H T X = angular_upperNoStopArity ℓ i κ ρ ξ H T X+
        angular_upperStoppedFilteredArity ℓ i κ ρ ξ H T X := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => angular_upperLowArity_stopping ℓ i ξ hκ
  filter_upwards [hall] with X hr
  intro ρ hρ hρ₂ H T
  unfold angular_upperLowTail angular_upperNoStopTail
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => hr i hi ρ hρ hρ₂ H T)

end CubicFirstMoment

end

end OAI
