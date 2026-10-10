import Mathlib
import OAI.Combinatorics.UniformKServer.TierParameters

namespace OAI

                                  
section

/-! The source's dyadic tiers, including the minimal last tier and the sharp
prefix/unqualified sums. These coefficients are summed before summing scales. -/
noncomputable section
namespace UniformKServer.DyadicTiers
open Finset
open scoped Classical

def value (i : ℕ) : ℝ := 2^i

theorem one_le_value (i : ℕ) : 1≤value i := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
theorem value_pos (i : ℕ) : 0<value i := lt_of_lt_of_le (by norm_num) (one_le_value i)

theorem unbounded (L : ℝ) : ∃ i : ℕ, L≤value i := by
  obtain ⟨n,hn⟩ := exists_nat_ge L
  refine ⟨n,hn.trans ?_⟩
  have hh : n≤(2:ℕ)^n := Nat.le_of_lt (Nat.lt_two_pow_self)
  dsimp only [value]
  exact_mod_cast hh

def last (L : ℝ) : ℕ := Nat.find (unbounded L)

theorem last_ge (L : ℝ) : L≤value (last L) := Nat.find_spec (unbounded L)

theorem before_last (L : ℝ) (i : ℕ) (hi : i<last L) : value i<L := by
  exact lt_of_not_ge (Nat.find_min (unbounded L) hi)

theorem last_mono (A B : ℝ) (hAB : A≤B) : last A≤last B := by
  exact Nat.find_min' (unbounded A) (hAB.trans (last_ge B))

theorem last_bound (L : ℝ) : value (last L)≤2*max 1 L := by
  cases he : last L with
  | zero => simp only [value,pow_zero]; linarith [le_max_left (1:ℝ) L]
  | succ i =>
    have hi := before_last L i (by omega)
    simp only [value,pow_succ] at hi ⊢
    linarith [le_max_right (1:ℝ) L]

theorem sum_exact (n : ℕ) : ∑ i∈range n, value i=2^n-1 := by
  have h := geom_sum_mul (2:ℝ) n
  norm_num only [show (2:ℝ)-1=1 by norm_num,mul_one] at h
  exact h

theorem prefix_sum (L : ℝ) : (∑ i∈range (last L+1), value i)≤4*max 1 L := by
  rw [sum_exact,pow_succ]
  have h := last_bound L
  dsimp only [value] at h
  linarith

theorem value_mono : Monotone value := by
  intro i j hij
  exact pow_le_pow_right₀ (by norm_num) hij

theorem unqualified_sum (L : ℝ) (hL : 0≤L) (n : ℕ) :
    (∑ i∈range n, if value i<L then value i else 0)≤2*L := by
  induction n with
  | zero => simp only [sum_range_zero]; linarith
  | succ n ih =>
    by_cases hn : value n<L
    · have hall : (∑ i∈range (n+1), if value i<L then value i else 0)=
          ∑ i∈range (n+1), value i := by
        apply sum_congr rfl
        intro i hi
        exact ite_eq_left ((value_mono (by have := mem_range.mp hi; omega)).trans_lt hn)
      rw [hall,sum_exact,pow_succ]
      dsimp only [value] at hn
      linarith
    · rw [sum_range_succ,ite_eq_right hn,add_zero]
      exact ih

theorem inverse_cutoff (C : ℝ) (hC : 1≤C) (i : ℕ) :
    1/(TierParameters.cutoff C (value i):ℝ)≤(1/2:ℝ)^i := by
  have hv := value_pos i
  have hc : value i≤(TierParameters.cutoff C (value i):ℝ) := by
    have he := Real.add_one_le_exp (C*value i)
    have hh := Nat.le_ceil (Real.exp (C*value i))
    change _≤(⌈Real.exp (C*value i)⌉₊:ℝ)
    nlinarith
  have hinv := one_div_le_one_div_of_le hv hc
  simpa only [one_div_pow,value] using hinv

theorem inverse_sum (C : ℝ) (hC : 1≤C) (n : ℕ) :
    (∑ i∈range n, 1/(TierParameters.cutoff C (value i):ℝ))≤2 := by
  exact (sum_le_sum (fun i _ => inverse_cutoff C hC i)).trans (sum_geometric_two_le n)

theorem exponential_sum (n : ℕ) : (∑ i∈range n, Real.exp (-value i))≤2 := by
  apply le_trans (sum_le_sum (fun i _ => ?_)) (sum_geometric_two_le n)
  have hi : (i:ℝ)≤value i := by
    dsimp only [value]
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self) : i≤2^i)
  have hl : Real.log 2≤1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have harg : -(value i)≤-(i:ℝ)*Real.log 2 := by
    have hn : (0:ℝ)≤ i := Nat.cast_nonneg _
    nlinarith
  have he := Real.exp_le_exp.mpr harg
  rw [show -(i:ℝ)*Real.log 2=(i:ℝ)*(-Real.log 2) by ring,Real.exp_nat_mul] at he
  simpa only [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),one_div] using he

end UniformKServer.DyadicTiers

end


end

end OAI
