import Mathlib

namespace OAI

section
namespace SharpLogRamsey.DyadicGrid
open Finset
open scoped BigOperators
noncomputable section

def value (i : ℕ) : ℝ := (1/2:ℝ)^i

lemma value_pos (i : ℕ) : 0<value i := by unfold value; positivity
lemma value_le_one (i : ℕ) : value i≤1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)
lemma value_succ (i : ℕ) : value (i+1)=value i/2 := by
  simp only [value,pow_succ,div_eq_mul_inv]; ring

lemma covers (m : ℕ) (y : ℝ) (hl : value m≤y) (hu : y≤2) :
    ∃ i ≤ m,value i≤y ∧ y≤2*value i := by
  induction m generalizing y with
  | zero => exact ⟨0,le_rfl,hl,by simpa [value] using hu⟩
  | succ m ih =>
    by_cases h : 1≤y
    · exact ⟨0,Nat.zero_le _,by simpa [value] using h,by simpa [value] using hu⟩
    · have hl' : value m≤2*y := by rw [value_succ] at hl; linarith
      obtain ⟨i,him,hiy,hyi⟩ := ih (2*y) hl' (by linarith)
      refine ⟨i+1,Nat.succ_le_succ him,?_,?_⟩ <;> rw [value_succ] <;> linarith

lemma sum_le_two (m : ℕ) : (∑ i∈range m,value i)≤2 := by
  have he : (∑ i∈range m,value i)=2*(1-value m) := by
    induction m with
    | zero => simp [value]
    | succ m ih => rw [sum_range_succ,ih,value_succ]; ring
  rw [he]
  have hp := (value_pos m).le
  linarith

lemma sum_pow_le_two (m r : ℕ) (hr : 1≤r) :
    (∑ i∈range m,(value i)^r)≤2 := by
  apply le_trans _ (sum_le_two m)
  exact sum_le_sum (fun i _ => pow_le_of_le_one (value_pos i).le (value_le_one i) (by omega))

lemma value_log_le {n : ℕ} (hn : 0<n) : value (Nat.log 2 n+1)≤1/(n:ℝ) := by
  have hp : n<2^(Nat.log 2 n+1) := Nat.lt_pow_succ_log_self (by omega) n
  have hp' : (n:ℝ)≤(2:ℝ)^(Nat.log 2 n+1) := by exact_mod_cast hp.le
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  simp only [value,one_div_pow]
  exact one_div_le_one_div_of_le hn' hp'

theorem integer_overlap_cover {n : ℕ} (hn : 0<n) (c : ℝ) (hc : 1/(n:ℝ)≤c)
    (k : ℕ) (hk : 0<k) (hu : c*k≤2) :
    ∃ i∈range (Nat.log 2 n+2),value i≤c*k ∧ c*k≤2*value i := by
  have hc0 : 0≤c := (by positivity : (0:ℝ)≤1/(n:ℝ)).trans hc
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hl : value (Nat.log 2 n+1)≤c*k :=
    (value_log_le hn).trans (hc.trans (by nlinarith))
  obtain ⟨i,hi,h1,h2⟩ := covers _ _ hl hu
  exact ⟨i,mem_range.mpr (by omega),h1,h2⟩

end
end SharpLogRamsey.DyadicGrid

end

end OAI
