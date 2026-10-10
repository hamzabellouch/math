import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedComparisonAbsorption

theorem universal_main_add_residual_le {r Δ C m e : ℝ}
    (hr : 1 ≤ r) (hΔ : 0 ≤ Δ) (hC : 0 ≤ C) (hm : 1 ≤ m) (he : e ≤ 1) :
    Real.exp (r*(Δ+C*m))+e ≤ Real.exp (r*(Δ+(C+1)*m)) := by
  have hr0 : 0 ≤ r := by linarith
  have hm0 : 0 ≤ m := by linarith
  have ha : 0 ≤ r*(Δ+C*m) := mul_nonneg hr0 (add_nonneg hΔ (mul_nonneg hC hm0))
  have hea : 1 ≤ Real.exp (r*(Δ+C*m)) := Real.one_le_exp ha
  have hrm : 1 ≤ r*m := by nlinarith
  have htwo : (2:ℝ) ≤ Real.exp (r*m) := by linarith [Real.add_one_le_exp (r*m)]
  calc
    _ ≤ 2*Real.exp (r*(Δ+C*m)) := by linarith
    _ ≤ Real.exp (r*m)*Real.exp (r*(Δ+C*m)) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem finite_sum_exp_reserve_le {ι : Type*} [Fintype ι]
    (F : ι→ℝ) (x m : ℝ) (hm : 1 ≤ m)
    (hF : ∀i,F i ≤ Real.exp (x-(Fintype.card ι:ℝ)*m)) :
    ∑i,F i ≤ Real.exp x := by
  have hc : 0 ≤ (Fintype.card ι:ℝ) := Nat.cast_nonneg _
  have hcm : (Fintype.card ι:ℝ) ≤ (Fintype.card ι:ℝ)*m := le_mul_of_one_le_right hc hm
  have hcap : (Fintype.card ι:ℝ) ≤ Real.exp ((Fintype.card ι:ℝ)*m) := by
    linarith [Real.add_one_le_exp ((Fintype.card ι:ℝ)*m)]
  calc
    _ ≤ ∑_i : ι,Real.exp (x-(Fintype.card ι:ℝ)*m) := Finset.sum_le_sum (fun i _=>hF i)
    _ = (Fintype.card ι:ℝ)*Real.exp (x-(Fintype.card ι:ℝ)*m) := by simp
    _ ≤ Real.exp ((Fintype.card ι:ℝ)*m)*Real.exp (x-(Fintype.card ι:ℝ)*m) :=
      mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem norm_sum_exp_reserve_le {ι : Type*} [Fintype ι]
    (F : ι→ℂ) (x m : ℝ) (hm : 1 ≤ m)
    (hF : ∀i,‖F i‖ ≤ Real.exp (x-(Fintype.card ι:ℝ)*m)) :
    ‖∑i,F i‖ ≤ Real.exp x :=
  (norm_sum_le _ _).trans (finite_sum_exp_reserve_le (fun i=>‖F i‖) x m hm hF)

end Ostmann.Arithmetic.HistorySelectedComparisonAbsorption

end

end OAI
