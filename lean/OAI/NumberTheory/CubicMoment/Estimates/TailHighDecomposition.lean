import OAI.NumberTheory.CubicMoment.Estimates.TailHighCollection
import OAI.NumberTheory.CubicMoment.Estimates.UpperLowTail
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstOrdinaryTail

namespace OAI

/-! Exact separation of the original prime Gauss tail into the two
low-scale contributions, the remaining prime groups, and semiprimes. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailHighOrdinaryArity (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      tailHighScaleRows i 0 ξ H (T*(3/2:ℝ)^s) X (X^(69/200:ℝ)) else 0

def tailHighUpperArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      tailHighScaleRows i 0 ξ H (T*(3/2:ℝ)^s) X (X^(1/3-2*κ)) else 0

lemma tailArity_height_scale_split (i : ℕ) (κ ξ H T X : ℝ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        scaleFirstTailScaleRow i 0 ξ H (T*(3/2:ℝ)^s) X d) =
      scaleFirstOrdinaryLowArity i ξ H T X + tailHighOrdinaryArity i ξ H T X +
        upperLowArity i κ ξ H T X + tailHighUpperArity i κ ξ H T X := by
  unfold scaleFirstOrdinaryLowArity tailHighOrdinaryArity upperLowArity tailHighUpperArity
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : T*(3/2:ℝ)^s ≤ X^(1/100:ℝ)
  · simp only [hs,not_lt.mpr hs,ite_true,ite_false,add_zero]
    exact tailHighScaleRows_window_split i 0 ξ H (T*(3/2:ℝ)^s) X _
  · simp only [hs,lt_of_not_ge hs,ite_true,ite_false,zero_add]
    exact tailHighScaleRows_window_split i 0 ξ H (T*(3/2:ℝ)^s) X _

theorem primeProductGaussTail_scale_decomposition {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ κ H T : ℝ,
      primeProductGaussTail 0 H T X =
        scaleFirstOrdinaryLowTail m ξ H T X +
        (∑ i ∈ Finset.range m, tailHighOrdinaryArity i ξ H T X) +
        upperLowTail m κ ξ H T X +
        (∑ i ∈ Finset.range m, tailHighUpperArity i κ ξ H T X) -
        ∑ s ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailSemiprimeWindow 0 H (T*(3/2:ℝ)^s) X := by
  obtain ⟨m,hm⟩ := scaleFirstTailRoughWindow_by_scale hξ hξz
  refine ⟨m,?_⟩
  filter_upwards [hm,primeProductGaussTail_detector 0] with X hrow hdet
  intro κ H T
  rw [hdet H T]
  congr 1
  simp_rw [hrow 0 H]
  rw [Finset.sum_comm]
  simp_rw [tailArity_height_scale_split (κ := κ)]
  simp only [Finset.sum_add_distrib,scaleFirstOrdinaryLowTail,upperLowTail]

end CubicFirstMoment

end

end OAI
