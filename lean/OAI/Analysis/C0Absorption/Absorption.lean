import OAI.Analysis.C0Absorption.Onto

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def absorptionK (x : C0 × BlockC0) : ConcreteSpace := concreteLift (inputCoordinates x)
def absorptionG (x : C0 × BlockC0) : BlockC0 := recomputedShift (inputCoordinates x)

theorem absorptionK_lipschitz : LipschitzWith 3 absorptionK := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := concreteLift_lipschitz.dist_le_mul (inputCoordinates x) (inputCoordinates y)
  rw [inputCoordinates.isometry.dist_eq] at h
  exact h

theorem absorptionG_surjective : Function.Surjective absorptionG :=
  recomputedShift_surjective.comp inputCoordinates.surjective

theorem absorptionG_lower (x y : C0 × BlockC0) :
    (22/125 : ℝ)*dist x y≤dist (absorptionG x) (absorptionG y) := by
  have h := (recomputed_global_bounds (inputCoordinates x) (inputCoordinates y)).1
  rw [inputCoordinates.isometry.dist_eq] at h
  norm_num [eta] at h
  exact h

theorem absorptionQK (x : C0 × BlockC0) : correctionQ (absorptionK x)=absorptionG x-x.2 := by
  rw [absorptionK,correctionQ_concreteLift]
  have he : inputBlocks (inputCoordinates x)=x.2 := by ext γ; exact joinInputs_block x γ
  rw [he]
  rfl

def concreteAbsorption : ConcreteSpace × C0 → ConcreteSpace := absorptionMap correctionQ absorptionK

theorem concreteAbsorption_surjective : Function.Surjective concreteAbsorption :=
  absorption_onto correctionQ absorptionK absorptionG absorptionG_surjective absorptionQK

theorem concreteAbsorption_upper (x y : ConcreteSpace × C0) :
    dist (concreteAbsorption x) (concreteAbsorption y)≤(1+3*max 1 ‖correctionQ‖)*dist x y :=
  absorption_upper correctionQ absorptionK (by norm_num) absorptionK_lipschitz.dist_le_mul x y

theorem concreteAbsorption_inverse_bound (x y : ConcreteSpace × C0) :
    dist x y≤ max (1+3*‖correctionQ‖/(22/125)) (‖correctionQ‖/(22/125))*
      dist (concreteAbsorption x) (concreteAbsorption y) :=
  absorption_inverse_bound correctionQ absorptionK absorptionG (by norm_num) (by norm_num)
    absorptionK_lipschitz.dist_le_mul absorptionG_lower absorptionQK x y

theorem concreteAbsorption_bilip : BiLip concreteAbsorption := by
  let D := max (1+3*‖correctionQ‖/(22/125)) (‖correctionQ‖/(22/125))
  let U := 1+3*max 1 ‖correctionQ‖
  have hD : 0<D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨1/D,max U (1/D),one_div_pos.mpr hD,le_max_right _ _,fun x y => ⟨?_,?_⟩⟩
  · have h := concreteAbsorption_inverse_bound x y
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using h)
  · exact (concreteAbsorption_upper x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)

def concreteC0Embedding (x : C0) : ConcreteSpace := concreteAbsorption (0,x)

theorem concreteC0Embedding_bilip : BiLip concreteC0Embedding := by
  obtain ⟨c,C,hc,hcC,h⟩ := concreteAbsorption_bilip
  refine ⟨c,C,hc,hcC,fun x y => ?_⟩
  simpa only [concreteC0Embedding,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using h (0,x) (0,y)

theorem noLinearC0_not_product_equiv {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (hZ : NoLinearC0 Z) : ¬ Nonempty ((Z × C0) ≃L[ℝ] Z) := by
  rintro ⟨e⟩
  let T : C0 →L[ℝ] Z := e.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Z C0)
  let B : ℝ := max 1 ‖e.symm.toContinuousLinearMap‖
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply hZ T
  refine ⟨1/B,one_div_pos.mpr hB,fun x => ?_⟩
  have hh : ‖x‖≤B*‖T x‖ := by
    calc
      ‖x‖ = ‖((0,x) : Z × C0)‖ := by simp
      _ = ‖e.symm (T x)‖ := by simp [T]
      _ ≤ ‖e.symm.toContinuousLinearMap‖*‖T x‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B*‖T x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  rw [one_div,mul_comm,← div_eq_mul_inv]
  exact (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hh)

theorem concrete_not_linearly_isomorphic : ¬ Nonempty ((ConcreteSpace × C0) ≃L[ℝ] ConcreteSpace) :=
  noLinearC0_not_product_equiv concrete_noLinearC0

end
end C0Absorption

end OAI
