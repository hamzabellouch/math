import OAI.NumberTheory.TotientAsymptotic.SurvivingSlack
import OAI.NumberTheory.TotientAsymptotic.GoodSlackBudget
import OAI.NumberTheory.TotientAsymptotic.ComparisonExponentSaving

namespace OAI

/-! The actual good-witness slack controls the constructed grid exponent. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma remainder_largest_factor_height_le {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hj : j ∈ Finset.Icc 1 (L x H)) :
    B (largestPrimeFactor (remainderPrime η j-1)) ≤ remainderCoord x η j := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hp3 := basic_remainder_prime_ge_three hη hj ((Finset.mem_Icc.mp hj).2.trans_lt hL)
  have hA : (1 : ℝ) < largestPrimeFactor (remainderPrime η j-1) := by
    exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ remainderPrime η j-1 by omega)
  have hle : (largestPrimeFactor (remainderPrime η j-1) : ℝ) ≤ remainderPrime η j := by
    have h := (largestPrimeFactor_le_self (show 1 ≤ remainderPrime η j-1 by omega)).trans (Nat.sub_le _ _)
    exact_mod_cast h
  simp only [remainderCoord,ite_eq_right hj0]
  exact Real.log_le_log (Real.log_pos hA) (Real.log_le_log (zero_lt_one.trans hA) hle)

/-- The sum uses the actual surviving indices, and retains the normalization
error between the original witness coordinate and the dyadic endpoint. -/
theorem actual_grid_weighted_slack {x y Z δ : ℝ} {H i p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x)
    (hg : GoodWitnessConditions p η) (hi : i ≤ R x H)
    (hk : collisionLastIndex x i < L x H)
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hh : 1 ≤ m x-i) (hBy : 0 < B y) (hδ : 0 < δ)
    (hcoord : remainderCoord x η i ≤ B y+1) (hinv : 1/B y ≤ δ)
    (ht : ComparisonHeightBounds (survivingPair p q η ξ i (collisionLastIndex x i)) (B y) Z)
    (halign : ∀ r, |leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r/B y-
      rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r/B y| ≤ (2*(r.val : ℝ)+1)*δ) :
    let t := survivingPair p q η ξ i (collisionLastIndex x i)
    let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
    (∑ r ∈ Finset.Icc 1 (b-1), a r*pairUpperCoordinates t y Z δ r) ≤
      1-1/((m x-i : ℕ) : ℝ)^4+δ+((2*(b : ℝ)+3)*δ)*(∑ r ∈ Finset.Icc 1 b, a r) := by
  dsimp only
  let t := survivingPair p q η ξ i (collisionLastIndex x i)
  let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
  let e := (2*(b : ℝ)+3)*δ
  let u := fun r => leftFactorHeight t r/B y
  let v := fun r => rightFactorHeight t r/B y
  obtain ⟨hb,hidx0⟩ := survivingIndex_first (Nat.le_add_right i _) hfirst
  change 0 < b at hb
  change survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩=i at hidx0
  have hbudget := good_slack_endpoint_budget hg hi hh hBy hcoord hinv
  have hw := surviving_weighted_slack hη hk hfirst (pairUpperCoordinates t y Z δ) hBy hbudget
    (by
      intro r hr
      have hrb : r < b := by have := Finset.mem_Icc.mp hr; omega
      have hoff := orderEmbedding_offset_le (survivingIndex p q η ξ i (collisionLastIndex x i)) hb hidx0 ⟨r,hrb⟩
      change i+r ≤ survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩ at hoff
      have hj := (Finset.mem_Icc.mp (Finset.mem_filter.mp
        (survivingIndex_mem p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩)).1).2
      have hj0 : survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩ ≠ 0 := by
        have := (Finset.mem_Icc.mp hr).1
        omega
      have hlo := remainder_largest_factor_height_le hη hL
        (Finset.mem_Icc.mpr ⟨by omega,hj.trans hk.le⟩)
      have he := paired_grid_approximation (ζ := (7/10 : ℝ)*Z/B y) hδ u v
        (fun r => div_nonneg (ht.positive r).1.le hBy.le)
        (fun r => div_nonneg (ht.positive r).2.le hBy.le) halign hr
      have hheight : leftFactorHeight t ⟨r,hrb⟩ ≤
          remainderCoord x η (survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩) := by
        simpa only [t,leftFactorHeight,survivingPair,wholeWitnessPrime,ite_eq_right hj0] using hlo
      exact he.trans (add_le_add (div_le_div_of_nonneg_right hheight hBy.le) (le_refl e)))
  have hsum : (∑ r ∈ Finset.Icc 1 (b-1), a r) ≤ ∑ r ∈ Finset.Icc 1 b, a r := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      have := Finset.mem_Icc.mp hr
      exact Finset.mem_Icc.mpr ⟨this.1,this.2.trans (Nat.sub_le _ _)⟩
    · intro r hr _
      exact (a_pos (Finset.mem_Icc.mp hr).1).le
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hs := mul_le_mul_of_nonneg_left hsum he0
  dsimp only [e] at hw hs
  linarith

/-- The constructed cutoffs have the strict exponent saving on the actual
collision witness, before the remaining polynomial factors are summed. -/
theorem actual_grid_exponent_saving {x y Z δ : ℝ} {H i p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x)
    (hg : GoodWitnessConditions p η) (hi : i ≤ R x H)
    (hk : collisionLastIndex x i < L x H)
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hh : 2 ≤ m x-i) (hBy : 0 < B y) (hδ : 0 < δ)
    (hδu : δ ≤ 2/((m x-i : ℕ) : ℝ)^32)
    (hcoord : remainderCoord x η i ≤ B y+1) (hinv : 1/B y ≤ δ)
    (ht : ComparisonHeightBounds (survivingPair p q η ξ i (collisionLastIndex x i)) (B y) Z)
    (halign : ∀ r, |leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r/B y-
      rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r/B y| ≤ (2*(r.val : ℝ)+1)*δ)
    (hbh : (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card ≤ m x-i)
    (hmesh : Real.sqrt (B (normalityScale x i)/B y)=δ) :
    let t := survivingPair p q η ξ i (collisionLastIndex x i)
    let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
    let Y := comparisonCutoffs y (pairUpperCoordinates t y Z δ)
    let U := comparisonCutoffs y (pairLowerCoordinates t y δ)
    (-2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+
      comparisonError b y (normalityScale x i) Y U ≤ -1-1/(2*((m x-i : ℕ) : ℝ)^4)) := by
  dsimp only
  apply comparison_exponent_saving hbh hh hδ.le hδu hmesh
  · have hw := actual_grid_weighted_slack hη hL hg hi hk hfirst (by omega) hBy hδ hcoord hinv ht halign
    simpa only [comparisonCutoffs_doubleLog hBy.ne'] using hw
  · intro j hj
    rw [comparisonCutoffs_doubleLog hBy.ne',comparisonCutoffs_doubleLog hBy.ne']
    have he := paired_grid_width δ ((7/10 : ℝ)*Z/B y)
      (pairGridLabel (survivingPair p q η ξ i (collisionLastIndex x i)) y δ) hj
    change pairedGridUpper δ ((7/10 : ℝ)*Z/B y)
        (pairGridLabel (survivingPair p q η ξ i (collisionLastIndex x i)) y δ) j-
      pairedGridLower δ (pairGridLabel (survivingPair p q η ξ i (collisionLastIndex x i)) y δ) j ≤ _
    rw [he]
    have hjb : (j : ℝ) ≤ (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card := by
      exact_mod_cast (Finset.mem_Icc.mp hj).2.trans (Nat.sub_le _ _)
    exact mul_le_mul_of_nonneg_right (by linarith) hδ.le

end TotientAsymptotic

end

end OAI
