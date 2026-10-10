import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.TimeChainPressureAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainModels.area {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : (l.map (fun p => p.1*(p.2:ℝ))).sum=∫ x in s..s+chainDuration l,α x := by
  induction l generalizing s with
  | nil => simp [chainDuration]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hcell : (∫ x in s..s+d,α x)=m*(d:ℝ) := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right d.coe_nonneg)
        (show (Ioo s (s+d)).EqOn α (fun _ => m) from fun x hx => hc x ⟨hx.1.le,hx.2⟩),intervalIntegral.integral_const]
      simp only [add_sub_cancel_left,smul_eq_mul,mul_comm]
    simp only [List.map_cons,List.sum_cons,chainDuration_cons,NNReal.coe_add]
    rw [ih ht,← add_assoc,← intervalIntegral.integral_add_adjacent_intervals
      (hα.intervalIntegrable (a:=s) (b:=s+d)) (hα.intervalIntegrable (a:=s+d) (b:=s+d+chainDuration l)),hcell]

theorem TimeChainModels.quadraticPenalty {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : chainQuadraticPenalty s l=2*∫ x in s..s+chainDuration l,x*α x := by
  have hi (a b : ℝ) : IntervalIntegrable (fun x => x*α x) volume a b :=
    hα.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  induction l generalizing s with
  | nil => simp [chainQuadraticPenalty,chainDuration]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hcell : (∫ x in s..s+d,x*α x)=m*((s+d)^2-s^2)/2 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right d.coe_nonneg)
        (show (Ioo s (s+d)).EqOn (fun x => x*α x) (fun x => x*m) from
          fun x hx => congrArg (fun y : ℝ => x*y) (hc x ⟨hx.1.le,hx.2⟩)),intervalIntegral.integral_mul_const,integral_id]
      ring
    simp only [chainQuadraticPenalty,chainDuration_cons,NNReal.coe_add]
    rw [ih ht,← add_assoc,← intervalIntegral.integral_add_adjacent_intervals (hi s (s+d)) (hi (s+d) (s+d+chainDuration l)),hcell]
    ring

end SK.Analytic

end
end

end OAI
