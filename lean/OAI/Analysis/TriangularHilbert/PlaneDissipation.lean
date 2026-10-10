import OAI.Analysis.TriangularHilbert.DissipationAlgebra

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def totalPlaneEnergy (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : ℝ :=
  ∑ v, planeIntegral (fun p => heatEnergy A h u p σ v) d

def totalPlaneTime (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (α : Three → ℝ) (s : ℝ) : ℝ :=
  ∑ v, ∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d

lemma totalPlaneEnergy_hasDerivAt (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => totalPlaneEnergy A h u d (fun w => α w*t))
      (totalPlaneTime A h u d α s) s := by
  exact HasDerivAt.fun_sum (fun v _ => planeEnergy_hasDerivAt_time A hh u d α hα hs v)

lemma two_totalPlaneTime (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) :
    2 * totalPlaneTime A h u d α s =
      ∑ v, ((∑ w, α w) * planeIntegral (fun p => heatMixed A h u p (fun a => α a*s) v (v+1) (v+2)) d -
        (∑ w, α w * planeIntegral (fun p => heatCost A h u p (fun a => α a*s) v w) d)) := by
  have hσ : ∀ w, 0 < α w*s := fun w => mul_pos (hα w) hs
  unfold totalPlaneTime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have hp := two_planeVariance A hh u d hσ v w
  rw [planePure_eq_mixed A hh u d hσ w (neighbor_one_ne v) (neighbor_two_ne v) (neighbors_ne v)] at hp
  linear_combination (α w)*hp

lemma plane_dissipation (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) :
    2 * totalPlaneTime A h u d α s ≤
      ∑ w, (-α w + Real.sqrt 2 * max 0 ((∑ v, α v)/2-α w)) *
        planeIntegral (fun p => heatCost A h u p (fun a => α a*s) w w) d := by
  have hσ : ∀ w, 0 < α w*s := fun w => mul_pos (hα w) hs
  rw [two_totalPlaneTime A hh u d α hα hs]
  apply finite_cost_dissipation α (fun w => (hα w).le)
  · exact fun v w => planeCost_nonneg A h u d _ v w
  · intro v
    rw [offdiag_sum_eq]
    exact two_planeMixed_le A hh u d hσ (neighbor_one_ne v) (neighbor_two_ne v) (neighbors_ne v)
  · exact planeCost_neighbors A hh u d hσ

def strictRate (i w : Three) : ℝ := if w = i then 1 else 11/10

def strictConstant : ℝ := (1/2) * min (1 - (3/5)*Real.sqrt 2) (11/10 - (1/2)*Real.sqrt 2)

lemma strictRate_pos (i w : Three) : 0 < strictRate i w := by
  unfold strictRate; split_ifs <;> norm_num

lemma sum_strictRate (i : Three) : (∑ w, strictRate i w) = 16/5 := by
  have he (w : Three) : strictRate i w = (11/10:ℝ) + if w = i then (-1/10:ℝ) else 0 := by
    unfold strictRate
    split_ifs <;> norm_num
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  norm_num [Finset.sum_ite_eq', Fintype.card_fin, Three]

lemma strictConstant_pos : 0 < strictConstant := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg (2:ℝ)
  have h1 : 0 < 1 - (3/5)*Real.sqrt 2 := by nlinarith
  have h2 : 0 < 11/10 - (1/2)*Real.sqrt 2 := by nlinarith
  exact mul_pos (by norm_num) (lt_min h1 h2)

lemma strictRate_coefficient (i w : Three) :
    -strictRate i w + Real.sqrt 2 * max 0 ((∑ v, strictRate i v)/2-strictRate i w) ≤
      -2 * strictConstant := by
  rw [sum_strictRate]
  have h1 := min_le_left (1 - (3/5)*Real.sqrt 2) (11/10 - (1/2)*Real.sqrt 2)
  have h2 := min_le_right (1 - (3/5)*Real.sqrt 2) (11/10 - (1/2)*Real.sqrt 2)
  unfold strictRate strictConstant
  split_ifs <;> norm_num <;> linarith

lemma plane_strict_dissipation (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (i : Three) {s : ℝ} (hs : 0 < s) :
    strictConstant * (∑ w, planeIntegral (fun p => heatCost A h u p (fun a => strictRate i a*s) w w) d) ≤
      -totalPlaneTime A h u d (strictRate i) s := by
  have hd := plane_dissipation A hh u d (strictRate i) (strictRate_pos i) hs
  have he : (∑ w, (-strictRate i w + Real.sqrt 2 * max 0 ((∑ v, strictRate i v)/2-strictRate i w)) *
        planeIntegral (fun p => heatCost A h u p (fun a => strictRate i a*s) w w) d) ≤
      -2 * strictConstant * (∑ w, planeIntegral (fun p => heatCost A h u p (fun a => strictRate i a*s) w w) d) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_right
      (strictRate_coefficient i w) (planeCost_nonneg A h u d _ w w))
  linarith
end
end TriangularHilbert.Heat
end

end OAI
