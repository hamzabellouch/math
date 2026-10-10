import OAI.Combinatorics.ContingencyTables.Rooted.RootedRootPenalty
import OAI.Combinatorics.ContingencyTables.Rooted.ForestScaledPenalty

namespace OAI

/-! # Convexity and the physical scaled Lipschitz bound for selected roots -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedRootPenalty
open ForestScaledPenalty (intervalCost intervalCost_nonnegative intervalCost_change
  intervalCost_combine free_card_le tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def normalizedOffset (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) : ℝ :=
  offset A S t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))/(A.b t.val.1 t.val.2:ℝ)

noncomputable def normalizedCoefficient (A : Instance I J) (S : Selection A.T)
    (B : ℝ) (t : TreeCell A.T) (f : FreeCell A.small A.T) : ℝ :=
  coefficient A S t f.val*((A.b f.val.1 f.val.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)

noncomputable def scaledTree (A : Instance I J) (S : Selection A.T)
    (B : ℝ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℝ) (t : TreeCell A.T) : ℝ :=
  AffinePenalty.affineValue (normalizedOffset A S t x q) (normalizedCoefficient A S B t) v

noncomputable def rootConstant (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) : ℝ :=
  ∑ a,if RootedPenalty.rootFlag S a then |(signedResidual A S x q 0 a:ℝ)| else 0

noncomputable def penalty (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℝ) : ℝ :=
  C*(rootConstant A S x q+∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q v t))

lemma penalty_nonnegative (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℝ) :
    0≤ penalty A S C B x q v := by
  unfold penalty rootConstant
  apply mul_nonneg hC
  apply add_nonneg
  · exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)
  · exact Finset.sum_nonneg (fun t _ => intervalCost_nonnegative _)

theorem penalty_change (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (x q : I → J → ℤ)
    (v w : FreeCell A.small A.T → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ f,|v f-w f|≤ r) :
    |penalty A S C B x q v-penalty A S C B x q w|≤(2*C*(A.d:ℝ)^2/B)*r := by
  have hterm (t : TreeCell A.T) :
      |intervalCost (scaledTree A S B x q v t)-intervalCost (scaledTree A S B x q w t)|≤
        (A.d:ℝ)*(2/B)*r := by
    apply (intervalCost_change _ _).trans
    have hh := AffinePenalty.affineValue_change (normalizedOffset A S t x q)
      (normalizedCoefficient A S B t) v w (2/B) r (by positivity)
      (fun f => normalized_coefficient_bound A S t f.val B hB) hvw
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast free_card_le A) (by positivity : (0:ℝ)≤2/B)) hr)
  have he : penalty A S C B x q v-penalty A S C B x q w=
      C*∑ t : TreeCell A.T,(intervalCost (scaledTree A S B x q v t)-
        intervalCost (scaledTree A S B x q w t)) := by
    unfold penalty
    rw [Finset.sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg hC]
  calc
    _≤ C*∑ t : TreeCell A.T,|intervalCost (scaledTree A S B x q v t)-
      intervalCost (scaledTree A S B x q w t)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hC
    _≤ C*∑ _t : TreeCell A.T,(A.d:ℝ)*(2/B)*r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hterm t)) hC
    _=C*((Fintype.card (TreeCell A.T):ℝ)*((A.d:ℝ)*(2/B)*r)) := by simp
    _≤ C*((A.d:ℝ)*((A.d:ℝ)*(2/B)*r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by exact_mod_cast tree_card_le A) (by positivity)) hC
    _=_ := by ring

theorem penalty_convex (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (x q : I → J → ℤ) :
    ConvexOn ℝ Set.univ (penalty A S C B x q) := by
  refine ⟨convex_univ,?_⟩
  intro v _ w _ a b ha hb hab
  have hsum : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q (a • v+b • w) t))≤
      a*(∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q v t))+
        b*(∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q w t)) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    unfold scaledTree
    rw [AffinePenalty.affineValue_combine _ _ _ _ _ _ hab]
    exact intervalCost_combine _ _ _ _ ha hb hab
  unfold penalty
  have hh := mul_le_mul_of_nonneg_left hsum hC
  simp only [smul_eq_mul]
  nlinarith [congrArg (fun z => C*z*rootConstant A S x q) hab]

theorem penalty_continuous (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (x q : I → J → ℤ) : Continuous (penalty A S C B x q) := by
  apply continuous_const.mul
  apply continuous_const.add
  apply continuous_finsetSum
  intro t _
  have hs : Continuous (fun v => scaledTree A S B x q v t) := by
    exact continuous_const.add (continuous_finsetSum Finset.univ
      (fun f _ => continuous_const.mul (continuous_apply f)))
  exact continuous_const.max (hs.neg.max (hs.sub continuous_const))

end ContingencyTables.RootedScaledPenalty

end OAI
