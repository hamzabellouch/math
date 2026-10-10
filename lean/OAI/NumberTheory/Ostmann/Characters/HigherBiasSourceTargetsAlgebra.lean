import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceTargets
open scoped BigOperators

def targetTail (k : ℕ) (c : ℕ→ℝ) (j : ℕ) : ℝ :=
  ∑i∈Finset.Ico j k,(2:ℝ)^(i-j)*c i

def target (k : ℕ) (c : ℕ→ℝ) (j : ℕ) : ℝ :=
  targetTail k c j-targetTail k c (j+1)

lemma targetTail_end (k : ℕ) (c : ℕ→ℝ) : targetTail k c k=0 := by simp [targetTail]

lemma targetTail_step {k j : ℕ} (hj : j<k) (c : ℕ→ℝ) :
    targetTail k c j=c j+2*targetTail k c (j+1) := by
  unfold targetTail
  rw [Finset.sum_eq_sum_Ico_succ_bot hj,Nat.sub_self,pow_zero,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hij := (Finset.mem_Ico.mp hi).1
  have he : i-j=(i-(j+1))+1 := by omega
  rw [he,pow_succ]
  ring

lemma target_eq {k j : ℕ} (hj : j<k) (c : ℕ→ℝ) :
    target k c j=c j+targetTail k c (j+1) := by
  rw [target,targetTail_step hj]
  ring

lemma sum_target {k j : ℕ} (hj : j≤k) (c : ℕ→ℝ) :
    ∑i∈Finset.Ico j k,target k c i=targetTail k c j := by
  have hh := Finset.sum_Ico_sub (fun i=>-targetTail k c i) hj
  simpa only [neg_sub_neg,targetTail_end,sub_zero,target] using hh

lemma target_recurrence {k j : ℕ} (hj : j<k) (c : ℕ→ℝ) :
    target k c j=c j+∑i∈Finset.Ico (j+1) k,target k c i := by
  rw [sum_target (by omega),target_eq hj]

lemma target_total (k : ℕ) (c : ℕ→ℝ) :
    ∑i∈Finset.range k,target k c i=∑i∈Finset.range k,(2:ℝ)^i*c i := by
  rw [Finset.range_eq_Ico,sum_target (Nat.zero_le k)]
  simp only [targetTail,Nat.sub_zero]

lemma targetTail_nonneg (k j : ℕ) (c : ℕ→ℝ) (hc : ∀i<k,0≤c i) :
    0≤targetTail k c j := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (hc i (Finset.mem_Ico.mp hi).2)

lemma target_nonneg {k j : ℕ} (hj : j<k) (c : ℕ→ℝ) (hc : ∀i<k,0≤c i) :
    0≤target k c j := by
  rw [target_eq hj]
  exact add_nonneg (hc j hj) (targetTail_nonneg k (j+1) c hc)

lemma target_le_total {k j : ℕ} (hj : j<k) (c : ℕ→ℝ) (hc : ∀i<k,0≤c i) :
    target k c j≤∑i∈Finset.range k,target k c i :=
  Finset.single_le_sum (fun _i hi=>target_nonneg (Finset.mem_range.mp hi) c hc)
    (Finset.mem_range.mpr hj)

lemma target_ge_last {k j : ℕ} (hj : j<k) (c : ℕ→ℝ) (hc : ∀i<k,0≤c i) :
    c (k-1)≤target k c j := by
  rw [target_eq hj]
  by_cases he : j=k-1
  · subst j
    exact le_add_of_nonneg_right (targetTail_nonneg k _ c hc)
  · have hjk : j+1≤k-1 := by omega
    have hm : k-1∈Finset.Ico (j+1) k := Finset.mem_Ico.mpr ⟨hjk,by omega⟩
    have hs : (2:ℝ)^((k-1)-(j+1))*c (k-1)≤targetTail k c (j+1) := by
      unfold targetTail
      exact Finset.single_le_sum
        (fun i hi=>mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) (i-(j+1)))
          (hc i (Finset.mem_Ico.mp hi).2)) hm
    have hpow : (1:ℝ)≤2^((k-1)-(j+1)) := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hpow (hc (k-1) (by omega))
    simp only [one_mul] at hh
    exact (hh.trans hs).trans (le_add_of_nonneg_left (hc j hj))

end Ostmann.Characters.HigherBiasSourceTargets

end

end OAI
