import OAI.Analysis.Cotype.Target
import Mathlib.Analysis.MeanInequalities

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype

theorem finite_l2_le_lq {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i)
    {q : ℝ} (hq : 2 ≤ q) :
    Real.sqrt (∑ i, x i ^ 2) ≤
      (m : ℝ)^(1/2-1/q) * (∑ i, x i ^ q)^(1/q) := by
  have hq0 : 0 < q := by linarith
  have hqne := ne_of_gt hq0
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := fun i => x i ^ 2) (by linarith : 1 ≤ q/2)
    (fun i hi => sq_nonneg (x i))
  have he (i : Fin m) : (x i ^ 2) ^ (q/2) = x i ^ q := by
    rw [← Real.rpow_two, ← Real.rpow_mul (hx i)]
    congr 1; ring
  simp only [he, Finset.card_univ, Fintype.card_fin] at h
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hs _) h (le_of_lt (one_div_pos.mpr hq0))
  have hp : (q/2)*(1/q) = (1/2 : ℝ) := by field_simp
  have hp' : (q/2-1)*(1/q) = (1/2-1/q : ℝ) := by field_simp
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg m) _)
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) _)),
    ← Real.rpow_mul hs, ← Real.rpow_mul (Nat.cast_nonneg m), hp, hp'] at hr
  simpa only [Real.sqrt_eq_rpow] using hr

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fixedCotypeBound_of_cotype_constant {q C : ℝ} (hq : 2 ≤ q) (hC : 0 ≤ C)
    (h : ∀ (n : ℕ) (x : Fin n → X),
      (∑ i, ‖x i‖ ^ q)^(1/q) ≤ C*cubeL2 X (rademacherSum X x)) (m : ℕ) :
    FixedCotypeBound X m (C*(m : ℝ)^(1/2-1/q)) := by
  refine ⟨mul_nonneg hC (Real.rpow_nonneg (by positivity) _),?_⟩
  intro x
  exact (finite_l2_le_lq (fun i => ‖x i‖) (fun i => norm_nonneg _) hq).trans
    (by simpa [mul_assoc, mul_comm C] using
      mul_le_mul_of_nonneg_left (h m x) (Real.rpow_nonneg (by positivity) (1/2-1/q)))

theorem finiteCotype_fixed_bounds (h : FiniteCotype X) :
    ∃ q C : ℝ, 2 ≤ q ∧ 1 ≤ C ∧ ∀ m,
      FixedCotypeBound X m (C*(m : ℝ)^(1/2-1/q)) := by
  obtain ⟨q,hq,C,hC,hbound⟩ := h
  refine ⟨q,max C 1,hq,le_max_right _ _,?_⟩
  intro m
  apply fixedCotypeBound_of_cotype_constant hq (le_trans (by norm_num) (le_max_right C 1))
  intro n x
  exact (hbound n x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))

end Cotype

end

end OAI
