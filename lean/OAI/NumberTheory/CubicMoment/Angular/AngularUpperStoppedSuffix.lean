import OAI.NumberTheory.CubicMoment.Angular.AngularUpperTailAggregation
import OAI.NumberTheory.CubicMoment.Estimates.UpperHeightSuffix

namespace OAI

/-! The upper portion of the actual stopped height sum is an aligned
full tail. This preserves cancellation when the ordinary heights are removed. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_upperStoppedWindow (i : ℕ) (κ ρ ξ H U X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(1/3-2*κ) then
      upperTailStoppedRow i ℓ κ ρ ξ H U X d else 0

def angular_upperStoppedFilteredArity (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      angular_upperStoppedWindow ℓ i κ ρ ξ H (T*(3/2:ℝ)^s) X else 0

lemma angular_upperStoppedWindow_sum (i : ℕ) (κ ρ ξ H T X : ℝ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      angular_upperStoppedWindow ℓ i κ ρ ξ H (T*(3/2:ℝ)^s) X) =
      angular_upperStoppedEnvelopeTail ℓ i κ ρ ξ H T X := by
  unfold angular_upperStoppedWindow angular_upperStoppedEnvelopeTail
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : distinguishedScaleLength d < X^(1/3-2*κ)
  · simp only [hd,ite_true]
  · simp only [hd,ite_false,Finset.sum_const_zero]

lemma angular_upperStoppedFilteredArity_suffix (i : ℕ) (κ ρ ξ H T X : ℝ)
    (hH : 0 < H) (hT : 0 < T) :
    ∃ j ≤ heightWindowCount H T,
      (j < heightWindowCount H T → X^(1/100:ℝ) < T*(3/2:ℝ)^j) ∧
      angular_upperStoppedFilteredArity ℓ i κ ρ ξ H T X =
        angular_upperStoppedEnvelopeTail ℓ i κ ρ ξ H (T*(3/2:ℝ)^j) X := by
  obtain ⟨j,hj,hstart,he⟩ := geometricHeight_filtered_suffix
    (fun U => angular_upperStoppedWindow ℓ i κ ρ ξ H U X) hH hT (X^(1/100:ℝ))
  exact ⟨j,hj,hstart,by simpa only [angular_upperStoppedFilteredArity,angular_upperStoppedWindow_sum ℓ] using he⟩

end CubicFirstMoment

end

end OAI
