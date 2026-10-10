import OAI.NumberTheory.CubicMoment.Estimates.UpperTailAggregation
import OAI.NumberTheory.CubicMoment.Estimates.UpperHeightSuffix

namespace OAI

/-! The upper portion of the actual stopped height sum is an aligned
full tail. This preserves cancellation when the ordinary heights are removed. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def upperStoppedWindow (i : ℕ) (κ ρ ξ H U X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(1/3-2*κ) then
      upperTailStoppedRow i 0 κ ρ ξ H U X d else 0

def upperStoppedFilteredArity (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      upperStoppedWindow i κ ρ ξ H (T*(3/2:ℝ)^s) X else 0

lemma upperStoppedWindow_sum (i : ℕ) (κ ρ ξ H T X : ℝ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      upperStoppedWindow i κ ρ ξ H (T*(3/2:ℝ)^s) X) =
      upperStoppedEnvelopeTail i κ ρ ξ H T X := by
  unfold upperStoppedWindow upperStoppedEnvelopeTail
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : distinguishedScaleLength d < X^(1/3-2*κ)
  · simp only [hd,ite_true]
  · simp only [hd,ite_false,Finset.sum_const_zero]

lemma upperStoppedFilteredArity_suffix (i : ℕ) (κ ρ ξ H T X : ℝ)
    (hH : 0 < H) (hT : 0 < T) :
    ∃ j ≤ heightWindowCount H T,
      (j < heightWindowCount H T → X^(1/100:ℝ) < T*(3/2:ℝ)^j) ∧
      upperStoppedFilteredArity i κ ρ ξ H T X =
        upperStoppedEnvelopeTail i κ ρ ξ H (T*(3/2:ℝ)^j) X := by
  obtain ⟨j,hj,hstart,he⟩ := geometricHeight_filtered_suffix
    (fun U => upperStoppedWindow i κ ρ ξ H U X) hH hT (X^(1/100:ℝ))
  exact ⟨j,hj,hstart,by simpa only [upperStoppedFilteredArity,upperStoppedWindow_sum] using he⟩

theorem upperStoppedFilteredArity_bounds (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1/12 ∧ ∀ (ρ ξ ε : ℝ),
      1 < ρ → ρ ≤ 2 → 0 ≤ ε → ρ ≤ (2:ℝ)^ε → ξ+ε < κ/2 →
      ∀ i n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T : ℝ),
        Real.log X ≤ T → 1 ≤ H → H ≤ X^(1/2:ℝ) →
        ‖upperStoppedFilteredArity i κ ρ ξ H T X‖ ≤
          K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨κ,hκ,hκsmall,hbound⟩ := upperStoppedEnvelopeTail_bounds hpnt hMV hC hHuxley
  refine ⟨κ,hκ,hκsmall,?_⟩
  intro ρ ξ ε hρ hρ₂ hε hsmall hgap i n
  obtain ⟨K,hK,hb⟩ := hbound ρ ξ ε hρ hρ₂ hε hsmall hgap i n
  refine ⟨K,hK,?_⟩
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with X hb hX
  intro H T hT hH hHX
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hTp : 0 < T := (Real.log_pos hX).trans_le hT
  obtain ⟨j,hj,hstart,he⟩ := upperStoppedFilteredArity_suffix i κ ρ ξ H T X hHp hTp
  by_cases hjN : j < heightWindowCount H T
  · rw [he]
    exact hb H (T*(3/2:ℝ)^j) (hstart hjN).le hH hHX
  · have hcount : heightWindowCount H (T*(3/2:ℝ)^j) = 0 := by
      rw [heightWindowCount_shift hHp hTp]
      omega
    rw [he,←upperStoppedWindow_sum]
    simp only [hcount,Finset.range_zero,Finset.sum_empty,norm_zero]
    have hL : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
    positivity

theorem upperStoppedFilteredTail_isLittleO (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1/12 ∧ ∀ (ρ ξ ε : ℝ),
      1 < ρ → ρ ≤ 2 → 0 ≤ ε → ρ ≤ (2:ℝ)^ε → ξ+ε < κ/2 →
      ∀ (m : ℕ) (H T : ℝ → ℝ),
        (∀ᶠ X : ℝ in atTop, Real.log X ≤ T X) →
        (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
        (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/2:ℝ)) →
        (fun X => ∑ i ∈ Finset.range m, upperStoppedFilteredArity i κ ρ ξ (H X) (T X) X)
          =o[atTop] firstMomentScale := by
  obtain ⟨κ,hκ,hκsmall,hbound⟩ := upperStoppedFilteredArity_bounds hpnt hMV hC hHuxley
  refine ⟨κ,hκ,hκsmall,?_⟩
  intro ρ ξ ε hρ hρ₂ hε hsmall hgap m H T hT hH hHX
  apply Asymptotics.IsLittleO.fun_sum
  intro i _hi
  obtain ⟨K,hK,hb⟩ := hbound ρ ξ ε hρ hρ₂ hε hsmall hgap i 3
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hb,hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X hb hT hH hHX hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  simpa only [Real.norm_of_nonneg (by positivity :
    0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3),mul_div_assoc] using hb (H X) (T X) hT hH hHX

end CubicFirstMoment

end

end OAI
