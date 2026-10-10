import OAI.Analysis.AncientFlat.Evolution.FiniteDifference

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace ParabolicInterpolation
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma multilinear_norm_le_unit {ι : Type*} [Fintype ι]
    (T : ContinuousMultilinearMap ℝ (fun _ : ι => V) E) (C : ℝ) (hC : 0≤C)
    (hT : ∀ v : ι → V, (∀ i, ‖v i‖≤1) → ‖T v‖≤C) : ‖T‖≤C := by
  classical
  apply T.opNorm_le_bound hC
  intro v
  by_cases hv : ∃ i, v i=0
  · obtain ⟨i,hi⟩ := hv
    rw [T.map_coord_zero i hi,norm_zero]
    positivity
  · push Not at hv
    let w : ι → V := fun i => ‖v i‖⁻¹ • v i
    have hw (i : ι) : ‖w i‖≤1 := by
      simp [w,norm_smul,norm_ne_zero_iff.mpr (hv i)]
    have he : v=fun i => ‖v i‖ • w i := by
      funext i
      simp [w,smul_smul,norm_ne_zero_iff.mpr (hv i)]
    have he' : T v=(∏ i, ‖v i‖) • T w := by
      conv_lhs => rw [he]
      rw [T.map_smul_univ]
    rw [he',norm_smul,Real.norm_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg _))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hT w hw)
      (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))

lemma jet_point_bound (n : ℕ) (f : V → E) (hf : ContDiff ℝ n f) (x : V)
    (q U A : ℝ) (hq : 0<q) (hU : 0≤U) (hA : 0≤A)
    (hu : ∀ y, ‖y-x‖≤n*q → ‖f y‖≤U)
    (ha : ∀ y, ‖y-x‖≤n*q → ‖iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f x‖≤A) :
    ‖iteratedFDeriv ℝ n f x‖≤2^n/q^n*U+A := by
  apply multilinear_norm_le_unit _ _ (by positivity)
  intro w hw
  let v : Fin n → V := fun i => q • w i
  have hv (i : Fin n) : ‖v i‖≤q := by
    simp only [v,norm_smul,Real.norm_of_nonneg hq.le]
    exact mul_le_of_le_one_right hq.le (hw i)
  have hs : (∑ i, ‖v i‖)≤n*q := by
    calc
      _≤∑ _i : Fin n, q := Finset.sum_le_sum (fun i _ => hv i)
      _=_ := by simp
  have hp : (∏ i, ‖v i‖)≤q^n := by
    calc
      _≤∏ _i : Fin n, q := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hv i)
      _=_ := by simp
  let F : V → E := fun y => iteratedFDeriv ℝ n f y v
  have hF : Continuous F := (hf.continuous_iteratedFDeriv le_rfl).eval_const _
  have hd : ‖difference n f v x‖≤2^n*U := norm_difference_le n f v x U hU (fun y hy => hu y (hy.trans hs))
  have he : ‖average n F v x-F x‖≤A*q^n := by
    rw [←average_const n (F x) v x,←average_sub n F (fun _ => F x) hF continuous_const]
    apply norm_average_le n _ v x _ (by positivity)
    intro y hy
    change ‖(iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f x) v‖≤_
    exact ((iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f x).le_opNorm v).trans
      (mul_le_mul (ha y (hy.trans hs)) hp (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hA)
  have hb : ‖F x‖≤2^n*U+A*q^n := by
    calc
      _≤‖average n F v x‖+‖average n F v x-F x‖ := norm_le_insert _ _
      _≤2^n*U+A*q^n := by
        apply add_le_add _ he
        change ‖average n (fun y => iteratedFDeriv ℝ n f y v) v x‖≤_
        rw [average_jet_eq_difference n f hf]
        exact hd
  have hFq : ‖F x‖=q^n*‖iteratedFDeriv ℝ n f x w‖ := by
    simp [F,v,ContinuousMultilinearMap.map_smul_univ,norm_smul,Real.norm_of_nonneg hq.le]
  rw [hFq] at hb
  apply (mul_le_mul_iff_right₀ (pow_pos hq n)).mp
  calc
    _≤2^n*U+A*q^n := by simpa only [mul_comm] using hb
    _=q^n*(2^n/q^n*U+A) := by field_simp [hq.ne']
end ParabolicInterpolation

end

end OAI
