import OAI.NumberTheory.JointDickman.Analysis.RieszUnsmoothCoefficients
import Mathlib.Analysis.Asymptotics.Defs

namespace OAI

/-! # Truncating the derivative polynomial at the desired asymptotic order -/
namespace JointDickman
open Finset Filter Asymptotics
open scoped Topology

theorem rieszLogDerivative_truncation_bound (b : ℕ → ℝ) (z : ℝ) (H K : ℕ) (hHK : H ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → 1 ≤ Real.log x →
      |rieszLogDerivative b z K x -
        x*∑ j ∈ range (H+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)| ≤
      C*x*(Real.log x)^(z-2-H) := by
  let c := rieszUnsmoothCoefficients b z
  let E := (z-1-(K:ℝ))*b K
  refine ⟨(∑ j ∈ Ico (H+1) (K+1), |c j|)+|E|,by positivity,?_⟩
  intro x hx hlog
  have hlog0 : 0 < Real.log x := by linarith
  have hsum : (∑ j ∈ range (K+1), c j*(Real.log x)^(z-1-j)) =
      (∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)) +
      ∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j) :=
    (sum_range_add_sum_Ico _ (Nat.add_le_add_right hHK 1)).symm
  rw [rieszLogDerivative_eq]
  change |x*((∑ j ∈ range (K+1), c j*(Real.log x)^(z-1-j))+
    E*(Real.log x)^(z-1-K-1)) - x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)| ≤ _
  rw [hsum]
  have heq : x*((∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j))+
      (∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j))+E*(Real.log x)^(z-1-K-1)) -
      x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j) =
      x*((∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j))+E*(Real.log x)^(z-1-K-1)) := by ring
  rw [heq,abs_mul,abs_of_pos hx]
  have hterms : |∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j)| ≤
      (∑ j ∈ Ico (H+1) (K+1), |c j|)*(Real.log x)^(z-2-H) := by
    calc
      _ ≤ ∑ j ∈ Ico (H+1) (K+1), |c j*(Real.log x)^(z-1-j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico (H+1) (K+1), |c j| *(Real.log x)^(z-2-H) := by
        apply sum_le_sum
        intro j hj
        rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hlog0.le _)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Real.rpow_le_rpow_of_exponent_le hlog
        have hj' : (H:ℝ)+1 ≤ j := by exact_mod_cast (mem_Ico.mp hj).1
        linarith
      _ = _ := (sum_mul ..).symm
  have hedge : |E*(Real.log x)^(z-1-K-1)| ≤ |E| *(Real.log x)^(z-2-H) := by
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hlog0.le _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hHK' : (H:ℝ) ≤ K := by exact_mod_cast hHK
    linarith
  calc
    _ ≤ x*(|∑ j ∈ Ico (H+1) (K+1), c j*(Real.log x)^(z-1-j)|+
        |E*(Real.log x)^(z-1-K-1)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hx.le
    _ ≤ x*((∑ j ∈ Ico (H+1) (K+1), |c j|)*(Real.log x)^(z-2-H)+
        |E| *(Real.log x)^(z-2-H)) := mul_le_mul_of_nonneg_left (add_le_add hterms hedge) hx.le
    _ = _ := by ring

theorem rieszLogDerivative_truncation (b : ℕ → ℝ) (z : ℝ) (H K : ℕ) (hHK : H ≤ K) :
    (fun x : ℝ => rieszLogDerivative b z K x -
      x*∑ j ∈ range (H+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) =O[atTop]
      (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨C,_,hb⟩ := rieszLogDerivative_truncation_bound b z H K hHK
  apply IsBigO.of_bound C
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hp : 0 ≤ x*(Real.log x)^(z-2-H) := by positivity
  simpa only [Real.norm_eq_abs,abs_of_nonneg hp,mul_assoc] using hb x hx hlog

end JointDickman

end OAI
