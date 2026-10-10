import Mathlib
import OAI.Combinatorics.KMedian.Optimization.FractionalDual

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def truncated (d : κ → ι → ℚ) (H : ℚ) (j : κ) (i : ι) : ℚ :=
  if d j i ≤ 1 then d j i else H

omit [Fintype ι] [Fintype κ] in
theorem truncated_bounds (d : κ → ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (j : κ) (i : ι) :
    0 ≤ truncated d H j i ∧ truncated d H j i ≤ H := by
  unfold truncated
  split_ifs with hi
  · exact ⟨hd j i,hi.trans hH⟩
  · exact ⟨(by linarith),le_rfl⟩

def objective (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ) : ℚ :=
  ∑ j, FractionalDual.value (truncated d H j) y H

def gradient (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ) (i : ι) : ℚ :=
  ∑ j, FractionalDual.gradient (truncated d H j) y H i

theorem subgradient (d : κ → ι → ℚ) (y z : ι → ℚ) (H : ℚ) :
    objective d y H-objective d z H ≤ ∑ i, gradient d y H i*(y i-z i) := by
  have hh := sum_le_sum (fun j (_ : j ∈ (univ:Finset κ)) =>
    FractionalDual.gradient_spec (truncated d H j) y z H)
  rw [sum_sub_distrib] at hh
  apply hh.trans_eq
  rw [sum_comm]
  exact sum_congr rfl (fun i _ => by rw [← sum_mul]; rfl)

theorem gradient_abs_bound (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (i : ι) :
    |gradient d y H i| ≤ (Fintype.card κ:ℚ)*H := by
  unfold gradient
  calc
    _ ≤ ∑ j, |FractionalDual.gradient (truncated d H j) y H i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H := sum_le_sum (fun j _ => FractionalDual.gradient_bound _ _ _
      (by linarith) (truncated_bounds d H hH hd j) i)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

theorem gradient_sq_bound (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) :
    (∑ i, (gradient d y H i)^2) ≤ (Fintype.card ι:ℚ)*((Fintype.card κ:ℚ)*H)^2 := by
  calc
    _ ≤ ∑ _i : ι, ((Fintype.card κ:ℚ)*H)^2 := sum_le_sum (fun i _ => by
      have hh := gradient_abs_bound d y H hH hd i
      have hh' := mul_self_le_mul_self (abs_nonneg (gradient d y H i)) hh
      simpa only [← sq, sq_abs] using hh')
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

theorem objective_le_assignment (d : κ → ι → ℚ) (y : ι → ℚ) (x : κ → ι → ℚ)
    (H : ℚ) (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) (hs : ∀ j, ∑ i, x j i=1) :
    objective d y H ≤ ∑ j, ∑ i, x j i*truncated d H j i :=
  sum_le_sum (fun j _ => FractionalDual.value_le_assignment _ _ _ _ (hx j) (hs j))

theorem objective_attained [DecidableEq ι] (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ)
    (hy : ∀ i, 0 ≤ y i) (hy1 : 1 ≤ ∑ i, y i) :
    ∃ x : κ → ι → ℚ, (∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) ∧
      (∀ j, ∑ i, x j i=1) ∧ (∑ j, ∑ i, x j i*truncated d H j i)=objective d y H := by
  choose x hx hs hc using (fun j => FractionalDual.value_attained (truncated d H j) y H hy hy1)
  exact ⟨x,hx,hs,sum_congr rfl (fun j _ => hc j)⟩

end MetricKMedian.TruncatedLP
end
end

end OAI
