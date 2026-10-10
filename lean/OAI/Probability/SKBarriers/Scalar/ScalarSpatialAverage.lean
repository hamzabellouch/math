import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFTerminalStability
import OAI.Probability.SKBarriers.Scalar.ScalarSusceptibilitySum
import OAI.Probability.SKBarriers.Scalar.ScalarAverageCalculus

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarHierarchyAverage_abs_le {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {C : ℝ} (hg : ∀ z, |g z| ≤ C) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x| ≤ C := by
  induction n generalizing f g with
  | zero => exact hg x
  | succ n ih =>
    exact ih (scalarStep_regular hf _ _) (scalarStepAverage_bound hf hg _ _) _ _

theorem scalarHierarchyAverage_spatial_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L C : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hgC : ∀ z, |g z| ≤ C) (x y : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f g y| ≤
      ((L:ℝ)+2*(C:ℝ)*Real.exp (2*(K:ℝ)))*|x-y| := by
  have hExp : 1 ≤ Real.exp (2*(K:ℝ)) := Real.one_le_exp (by positivity)
  by_cases hd : |x-y| ≤ 1
  · have H := scalarHierarchyAverage_terminal_stability n m v hm hmono
      (hf.translate x) (hf.translate y) (by positivity : 0 ≤ (K:ℝ)*|x-y|)
      (fun z => by simpa only [Real.norm_eq_abs, add_sub_add_right_eq_sub] using
        hfK.norm_sub_le (x+z) (y+z))
      (hgL.continuous.comp (continuous_const.add continuous_id))
      (hgL.continuous.comp (continuous_const.add continuous_id))
      C.coe_nonneg (fun z => hgC (x+z)) (fun z => hgC (y+z))
      (fun z => by simpa only [Function.comp_apply, Pi.add_apply, id_eq, Real.norm_eq_abs,add_sub_add_right_eq_sub] using
        hgL.norm_sub_le (x+z) (y+z)) 0
    change |scalarHierarchyAverage n m v (fun z => f (x+z)) (fun z => g (x+z)) 0 -
      scalarHierarchyAverage n m v (fun z => f (y+z)) (fun z => g (y+z)) 0| ≤ _ at H
    rw [scalarHierarchyAverage_translate,scalarHierarchyAverage_translate] at H
    simp only [add_zero] at H
    have E := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (2*(K:ℝ)))
      (by linarith : 0 ≤ 1-|x-y|) (abs_nonneg (x-y)) (by ring : 1-|x-y|+|x-y|=1)
    simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at E
    have Ee : Real.exp (2*((K:ℝ)*|x-y|))-1 ≤ Real.exp (2*(K:ℝ))*|x-y| := by
      rw [show 2*((K:ℝ)*|x-y|)=|x-y| *(2*(K:ℝ)) by ring]
      nlinarith [abs_nonneg (x-y)]
    have E2 := mul_le_mul_of_nonneg_left Ee (by positivity : 0 ≤ 2*(C:ℝ))
    nlinarith
  · have H := (abs_sub (scalarHierarchyAverage n m v f g x)
        (scalarHierarchyAverage n m v f g y)).trans
      (add_le_add (scalarHierarchyAverage_abs_le hf hgC n m v x)
        (scalarHierarchyAverage_abs_le hf hgC n m v y))
    have hlow : 2*(C:ℝ) ≤ (L:ℝ)+2*(C:ℝ)*Real.exp (2*(K:ℝ)) := by
      have := mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ 2*(C:ℝ))
      linarith [L.coe_nonneg]
    have H2 := hlow.trans (le_mul_of_one_le_right (by positivity) (le_of_not_ge hd))
    linarith

end SK.Analytic

end
end

end OAI
