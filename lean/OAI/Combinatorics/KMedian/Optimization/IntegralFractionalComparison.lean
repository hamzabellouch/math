import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ApproximateFractional

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

omit [NeZero n] [NeZero m] in

theorem integral_comparison (d : Fin m → Fin n → ℚ) (k : ℕ)
    (hd : ∀ j i, 0 ≤ d j i) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSk : S.card ≤ k) (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : (∑ j, d j (a j)) ≤ 1) (H : ℚ) :
    ∃ z : Fin n → ℚ, feasible (k:ℚ) z ∧ objective d z H ≤ ∑ j, d j (a j) := by
  classical
  obtain ⟨i₀,hi₀⟩ := hS
  let z : Fin n → ℚ := fun i => (if i ∈ S then 1 else 0)+
    (if i=i₀ then (k:ℚ)-(S.card:ℚ) else 0)
  have hrest : (0:ℚ) ≤ (k:ℚ)-(S.card:ℚ) := by
    have hh : (S.card:ℚ) ≤ k := by exact_mod_cast hSk
    linarith
  have hz0 : ∀ i, 0 ≤ z i := by
    intro i
    dsimp [z]
    split_ifs <;> linarith
  have hzs : (∑ i, z i)=(k:ℚ) := by
    simp only [z,sum_add_distrib,sum_ite_mem,sum_const,nsmul_eq_mul,
      sum_ite_eq',mem_univ,ite_true]
    simp
  have hza : ∀ j, 1 ≤ z (a j) := by
    intro j
    dsimp [z]
    rw [ite_eq_left (ha j)]
    split_ifs <;> linarith
  let x : Fin m → Fin n → ℚ := fun j i => if i=a j then 1 else 0
  have hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ z i := by
    intro j i
    dsimp [x]
    by_cases he : i=a j
    · rw [ite_eq_left he,he]; exact ⟨by norm_num,hza j⟩
    · rw [ite_eq_right he]; exact ⟨le_rfl,hz0 i⟩
  have hs : ∀ j, ∑ i, x j i=1 := by intro j; simp [x]
  have edge : ∀ j, d j (a j) ≤ 1 := by
    intro j
    exact (single_le_sum (fun j _ => hd j (a j)) (mem_univ j)).trans hc
  refine ⟨z,⟨hz0,hzs⟩,(objective_le_assignment d z x H hx hs).trans_eq ?_⟩
  apply sum_congr rfl
  intro j _
  simp only [x,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true,
    truncated,ite_eq_left (edge j)]

theorem approximation_integral (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc0 : 1/2 ≤ ∑ j, d j (a j)) (hc1 : (∑ j, d j (a j)) ≤ 1) :
    let out := approximation d r k hr hk hd
    (∀ i : Fin n, 0 ≤ out.opening[i.val] ∧ out.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ out.assignment[j.val][i.val] ∧
      out.assignment[j.val][i.val] ≤ out.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, out.opening[i.val]) ≤ (k:ℚ)+1 ∧
    (∑ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]*d j i) ≤
      (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨z,hz,hzc⟩ := integral_comparison d k hd S hS hSk a ha hc1 (penalty r k)
  exact approximation_spec d r k hr hk hd _ hc0 hc1 z hz hzc

end MetricKMedian.TruncatedLP
end
end

end OAI
