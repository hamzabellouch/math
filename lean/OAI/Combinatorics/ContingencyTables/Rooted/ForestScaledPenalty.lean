import OAI.Combinatorics.ContingencyTables.Rooted.ForestAffineCompletion
import OAI.Combinatorics.ContingencyTables.Rooted.ForestRootPenalty

namespace OAI

/-! # Convexity and the actual scaled forest-penalty Lipschitz bound -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def intervalCost (x : ℝ) : ℝ := max 0 (max (-x) (x-1))

lemma intervalCost_nonnegative (x : ℝ) : 0 ≤ intervalCost x := le_max_left _ _

lemma intervalCost_change (x y : ℝ) : |intervalCost x-intervalCost y| ≤ |x-y| := by
  have hsub (x y : ℝ) : intervalCost x ≤ intervalCost y+|x-y| := by
    unfold intervalCost
    apply max_le
    · linarith [le_max_left (0:ℝ) (max (-y) (y-1)),abs_nonneg (x-y)]
    · apply max_le
      · have hh : -y ≤ max 0 (max (-y) (y-1)) :=
          (le_max_left _ _).trans (le_max_right _ _)
        linarith [neg_le_abs (x-y)]
      · have hh : y-1 ≤ max 0 (max (-y) (y-1)) :=
          (le_max_right _ _).trans (le_max_right _ _)
        linarith [le_abs_self (x-y)]
  apply abs_le.mpr
  constructor
  · have hh := hsub y x
    rw [abs_sub_comm y x] at hh
    linarith
  · linarith [hsub x y]

lemma intervalCost_combine (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    intervalCost (a*x+b*y) ≤ a*intervalCost x+b*intervalCost y := by
  have hx0 := intervalCost_nonnegative x
  have hy0 := intervalCost_nonnegative y
  have hxl : -x ≤ intervalCost x := (le_max_left _ _).trans (le_max_right _ _)
  have hyl : -y ≤ intervalCost y := (le_max_left _ _).trans (le_max_right _ _)
  have hxu : x-1 ≤ intervalCost x := (le_max_right _ _).trans (le_max_right _ _)
  have hyu : y-1 ≤ intervalCost y := (le_max_right _ _).trans (le_max_right _ _)
  change max 0 (max (-(a*x+b*y)) (a*x+b*y-1)) ≤ a*intervalCost x+b*intervalCost y
  apply max_le
  · exact add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
  · apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left hxl ha,mul_le_mul_of_nonneg_left hyl hb]
    · nlinarith [mul_le_mul_of_nonneg_left hxu ha,mul_le_mul_of_nonneg_left hyu hb]

noncomputable def normalizedOffset (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℤ) : ℝ :=
  offset A t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))/(A.b t.val.1 t.val.2:ℝ)

noncomputable def normalizedCoefficient (A : Instance I J) (B : ℝ) (t : TreeCell A.T)
    (f : FreeCell A.small A.T) : ℝ :=
  coefficient A t f.val*((A.b f.val.1 f.val.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)

noncomputable def scaledTree (A : Instance I J) (B : ℝ) (x q : I → J → ℤ)
    (v : FreeCell A.small A.T → ℝ) (t : TreeCell A.T) : ℝ :=
  AffinePenalty.affineValue (normalizedOffset A t x q) (normalizedCoefficient A B t) v

noncomputable def rootConstant (A : Instance I J) (x q : I → J → ℤ) : ℝ :=
  ∑ a,if ForestPenaltyApplication.rootFlag A.T a then
    |(signedResidual A.small A.T A.r A.c x q 0 a:ℝ)| else 0

noncomputable def penalty (A : Instance I J) (C B : ℝ) (x q : I → J → ℤ)
    (v : FreeCell A.small A.T → ℝ) : ℝ :=
  C*(rootConstant A x q+∑ t : TreeCell A.T,intervalCost (scaledTree A B x q v t))

lemma penalty_nonnegative (A : Instance I J) (C B : ℝ) (hC : 0 ≤ C)
    (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℝ) :
    0 ≤ penalty A C B x q v := by
  unfold penalty rootConstant
  apply mul_nonneg hC
  apply add_nonneg
  · exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)
  · exact Finset.sum_nonneg (fun t _ => intervalCost_nonnegative _)

lemma free_card_le (A : Instance I J) : Fintype.card (FreeCell A.small A.T) ≤ A.d := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

lemma tree_card_le (A : Instance I J) : Fintype.card (TreeCell A.T) ≤ A.d := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

/-- All coefficients are obtained from the actual maximum-forest cuts.
The bound is 2*C*d²/B, which equals 1/8 for the source B=16*C*d². -/
theorem penalty_change (A : Instance I J) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 < B)
    (x q : I → J → ℤ) (v w : FreeCell A.small A.T → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hvw : ∀ f,|v f-w f| ≤ r) :
    |penalty A C B x q v-penalty A C B x q w| ≤ (2*C*(A.d:ℝ)^2/B)*r := by
  have hterm (t : TreeCell A.T) :
      |intervalCost (scaledTree A B x q v t)-intervalCost (scaledTree A B x q w t)| ≤
        (A.d:ℝ)*(2/B)*r := by
    apply (intervalCost_change _ _).trans
    have hh := AffinePenalty.affineValue_change (normalizedOffset A t x q)
      (normalizedCoefficient A B t) v w (2/B) r (by positivity)
      (fun f => normalized_coefficient_bound A t f.val B hB) hvw
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast free_card_le A) (by positivity : (0:ℝ) ≤ 2/B)) hr)
  have he : penalty A C B x q v-penalty A C B x q w=
      C*∑ t : TreeCell A.T,(intervalCost (scaledTree A B x q v t)-intervalCost (scaledTree A B x q w t)) := by
    unfold penalty
    rw [Finset.sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg hC]
  calc
    _ ≤ C*∑ t : TreeCell A.T,|intervalCost (scaledTree A B x q v t)-intervalCost (scaledTree A B x q w t)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hC
    _ ≤ C*∑ _t : TreeCell A.T,(A.d:ℝ)*(2/B)*r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hterm t)) hC
    _ = C*((Fintype.card (TreeCell A.T):ℝ)*((A.d:ℝ)*(2/B)*r)) := by simp
    _ ≤ C*((A.d:ℝ)*((A.d:ℝ)*(2/B)*r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by exact_mod_cast tree_card_le A) (by positivity)) hC
    _ = _ := by ring

theorem penalty_convex (A : Instance I J) (C B : ℝ) (hC : 0 ≤ C) (x q : I → J → ℤ) :
    ConvexOn ℝ Set.univ (penalty A C B x q) := by
  refine ⟨convex_univ,?_⟩
  intro v _ w _ a b ha hb hab
  have hsum : (∑ t : TreeCell A.T,intervalCost (scaledTree A B x q (a • v+b • w) t)) ≤
      a*(∑ t : TreeCell A.T,intervalCost (scaledTree A B x q v t))+
        b*(∑ t : TreeCell A.T,intervalCost (scaledTree A B x q w t)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    unfold scaledTree
    rw [AffinePenalty.affineValue_combine _ _ _ _ _ _ hab]
    exact intervalCost_combine _ _ _ _ ha hb hab
  unfold penalty
  have hh := mul_le_mul_of_nonneg_left hsum hC
  simp only [smul_eq_mul]
  nlinarith [congrArg (fun z => C*z*rootConstant A x q) hab]

theorem penalty_continuous (A : Instance I J) (C B : ℝ) (x q : I → J → ℤ) :
    Continuous (penalty A C B x q) := by
  apply continuous_const.mul
  apply continuous_const.add
  apply continuous_finsetSum
  intro t _
  have hs : Continuous (fun v => scaledTree A B x q v t) := by
    exact continuous_const.add (continuous_finsetSum Finset.univ
      (fun f _ => continuous_const.mul (continuous_apply f)))
  exact continuous_const.max (hs.neg.max (hs.sub continuous_const))

end ContingencyTables.ForestScaledPenalty

end OAI
