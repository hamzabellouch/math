import OAI.NumberTheory.CubicMoment.Estimates.TailHighCollection
import OAI.NumberTheory.CubicMoment.Angular.AngularUpperLowTail
import OAI.NumberTheory.CubicMoment.Angular.AngularOrdinaryTail

namespace OAI

/-! Exact separation of the original prime Gauss tail into the two
low-scale contributions, the remaining prime groups, and semiprimes. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_tailHighOrdinaryArity (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      tailHighScaleRows i ℓ ξ H (T*(3/2:ℝ)^s) X (X^(69/200:ℝ)) else 0

def angular_tailHighUpperArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      tailHighScaleRows i ℓ ξ H (T*(3/2:ℝ)^s) X (X^(1/3-2*κ)) else 0

lemma angular_tailArity_height_scale_split (i : ℕ) (κ ξ H T X : ℝ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        scaleFirstTailScaleRow i ℓ ξ H (T*(3/2:ℝ)^s) X d) =
      angular_scaleFirstOrdinaryLowArity ℓ i ξ H T X + angular_tailHighOrdinaryArity ℓ i ξ H T X +
        angular_upperLowArity ℓ i κ ξ H T X + angular_tailHighUpperArity ℓ i κ ξ H T X := by
  unfold angular_scaleFirstOrdinaryLowArity angular_tailHighOrdinaryArity angular_upperLowArity angular_tailHighUpperArity
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : T*(3/2:ℝ)^s ≤ X^(1/100:ℝ)
  · simp only [hs,not_lt.mpr hs,ite_true,ite_false,add_zero]
    exact tailHighScaleRows_window_split i ℓ ξ H (T*(3/2:ℝ)^s) X _
  · simp only [hs,lt_of_not_ge hs,ite_true,ite_false,zero_add]
    exact tailHighScaleRows_window_split i ℓ ξ H (T*(3/2:ℝ)^s) X _

theorem angular_primeProductGaussTail_scale_decomposition {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ κ H T : ℝ,
      primeProductGaussTail ℓ H T X =
        angular_scaleFirstOrdinaryLowTail ℓ m ξ H T X +
        (∑ i ∈ Finset.range m, angular_tailHighOrdinaryArity ℓ i ξ H T X) +
        angular_upperLowTail ℓ m κ ξ H T X +
        (∑ i ∈ Finset.range m, angular_tailHighUpperArity ℓ i κ ξ H T X) -
        ∑ s ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailSemiprimeWindow ℓ H (T*(3/2:ℝ)^s) X := by
  obtain ⟨m,hm⟩ := scaleFirstTailRoughWindow_by_scale hξ hξz
  refine ⟨m,?_⟩
  filter_upwards [hm,primeProductGaussTail_detector ℓ] with X hrow hdet
  intro κ H T
  rw [hdet H T]
  congr 1
  simp_rw [hrow ℓ H]
  rw [Finset.sum_comm]
  simp_rw [angular_tailArity_height_scale_split ℓ (κ := κ)]
  simp only [Finset.sum_add_distrib,angular_scaleFirstOrdinaryLowTail,angular_upperLowTail]

end CubicFirstMoment

end

end OAI
