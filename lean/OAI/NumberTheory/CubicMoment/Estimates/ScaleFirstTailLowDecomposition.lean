import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailAggregation

namespace OAI

/-! The exact low scale-first height-tail decomposition, retaining the
no-stop term and both original stopped branches. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstTailLow (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailScaleRow i 0 ξ H (T*(3/2:ℝ)^s) X d
    else 0

def scaleFirstTailNoStop (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailNoStopRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h d
    else 0

theorem scaleFirstTailLow_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ (H T : ℝ) (h : ℕ),
      scaleFirstTailLow i ξ H T X = scaleFirstTailNoStop i ρ ξ H T X h+
        scaleFirstStoppedEnvelopeTail i ρ ξ H T X h true+
        scaleFirstStoppedEnvelopeTail i ρ ξ H T X h false := by
  filter_upwards [scaleFirstTailScaleRow_two_stage i ξ] with X hrow
  intro ρ hρ hρ₂ H T h
  calc
    _ = ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        ((if distinguishedScaleLength d < X^(69/200:ℝ) then
          ∑ s ∈ Finset.range (heightWindowCount H T),
            scaleFirstTailNoStopRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h d else 0)+
        (if distinguishedScaleLength d < X^(69/200:ℝ) then
          ∑ s ∈ Finset.range (heightWindowCount H T),
            scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h true d else 0)+
        (if distinguishedScaleLength d < X^(69/200:ℝ) then
          ∑ s ∈ Finset.range (heightWindowCount H T),
            scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h false d else 0)) := by
      unfold scaleFirstTailLow
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : distinguishedScaleLength d < X^(69/200:ℝ)
      · simp only [hd,ite_true]
        rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s _
        exact hrow ρ hρ hρ₂ 0 H (T*(3/2:ℝ)^s) h d hd
      · simp only [hd,ite_false,zero_add]
    _ = _ := by
      simp only [Finset.sum_add_distrib,scaleFirstTailNoStop,scaleFirstStoppedEnvelopeTail]

end CubicFirstMoment

end

end OAI
