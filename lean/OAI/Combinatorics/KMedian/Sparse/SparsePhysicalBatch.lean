import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalBatchLaw
import OAI.Combinatorics.KMedian.Sparse.SparseFiltered
import OAI.Combinatorics.KMedian.Sparse.SparseMixture

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

def balanced (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) : Finset (Fin n) :=
  (univ.filter (fun e => ω e=true ∧ ∀ f∈C e, ω f=false)) ∩ Z

def unbalanced (Z : Finset (Fin n)) (ω : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun e => ω e=true ∧ e∉Z)

def law (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    SparseIntegerLaw (Finset (Fin n)) :=
  SparseIntegerLaw.mix
    ((SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).map (balanced Z C))
    ((SparseBernoulli.run (d := 4) q hq n).map (unbalanced Z))

theorem balanced_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) :
    balanced Z C ω=PhysicalBatchLaw.balanced Z C ω := by
  ext e
  simp only [balanced,PhysicalBatchLaw.balanced,FiniteLaw.selected,mem_inter,mem_filter]

theorem unbalanced_eq (Z : Finset (Fin n)) (ω : Fin n → Bool) :
    unbalanced Z ω=PhysicalBatchLaw.unbalanced Z ω := rfl

theorem length (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    (law Z C p q hp hq).length ≤ 2*((n+1)^4+1) := by
  rw [law,SparseIntegerLaw.mix_length]
  exact (add_le_add (SparseBernoulli.run_length _ _ n)
    (SparseBernoulli.run_length _ _ n)).trans_eq (two_mul _).symm

theorem prob_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset (Fin n) → Prop) [DecidablePred R] :
    (law Z C p q hp hq).real.prob R=
      (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseBernoulli.run (d := 4) q hq n).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  rw [law,SparseIntegerLaw.prob_mix,SparseIntegerLaw.prob_map,SparseIntegerLaw.prob_map]
  apply congrArg₂ (fun x y : ℝ => (1/2)*x+(1/2)*y)
  · apply FiniteLaw.prob_congr
    intro ω
    rw [balanced_eq]
  · apply FiniteLaw.prob_congr
    intro ω
    rw [unbalanced_eq]

theorem marginal (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (e : Fin n) :
    (law Z C p q hp hq).real.prob (fun A => e∈A)=
      if e∈Z then (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => e∈FiniteLaw.selected C ω) else (1/2)*(q e:ℝ) := by
  rw [prob_eq]
  by_cases he : e∈Z
  · simp only [PhysicalBatchLaw.balanced,PhysicalBatchLaw.unbalanced,mem_inter,mem_filter,
      mem_univ,he,and_true,not_true_eq_false,and_false,ite_true,FiniteLaw.prob_false,mul_zero,add_zero]
  · simp only [PhysicalBatchLaw.balanced,PhysicalBatchLaw.unbalanced,mem_inter,mem_filter,
      mem_univ,true_and,he,and_false,not_false_eq_true,and_true,ite_false,FiniteLaw.prob_false,
      SparseBernoulli.real_marginal q hq (by norm_num : 1 ≤ 4),mul_zero,zero_add]

theorem pair_le (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (e f : Fin n) (hef : e≠f) :
    (law Z C p q hp hq).real.prob (fun A => e∈A ∧ f∈A) ≤
      ((p:ℝ)^2+(q e:ℝ)*(q f:ℝ))/2 := by
  rw [prob_eq]
  have hb : (SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
      (fun ω => e∈PhysicalBatchLaw.balanced Z C ω ∧ f∈PhysicalBatchLaw.balanced Z C ω) ≤ (p:ℝ)^2 := by
    calc
      _ ≤ (SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
          (fun ω => ω e=true ∧ ω f=true) := by
        apply FiniteLaw.prob_mono
        intro ω h
        simp only [PhysicalBatchLaw.balanced,FiniteLaw.selected,mem_inter,mem_filter,mem_univ,true_and] at h
        exact ⟨h.1.1.1,h.2.1.1⟩
      _ = _ := by rw [SparseBernoulli.real_pair _ _ (by norm_num : 2 ≤ 4) e f hef,pow_two]
  have hu : (SparseBernoulli.run (d := 4) q hq n).real.prob
      (fun ω => e∈PhysicalBatchLaw.unbalanced Z ω ∧ f∈PhysicalBatchLaw.unbalanced Z ω) ≤
        (q e:ℝ)*(q f:ℝ) := by
    rw [← SparseBernoulli.real_pair q hq (by norm_num : 2 ≤ 4) e f hef]
    apply FiniteLaw.prob_mono
    intro ω h
    exact ⟨(mem_filter.mp h.1).2.1,(mem_filter.mp h.2).2.1⟩
  linarith only [hb,hu]

theorem marginal_error (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hqq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e∉C e) (e : Fin n) :
    |(law Z C p q hp hq).real.prob (fun A => e∈A)-(p:ℝ)/2| ≤
      (N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2 := by
  rw [marginal]
  have hp0 : (0:ℝ) ≤ p := by exact_mod_cast hp.1
  have hnonneg := mul_nonneg hφ hp0
  have hN0 : 0 ≤ (N:ℝ)*(p:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (p:ℝ))
  by_cases he : e∈Z
  · rw [ite_eq_left he]
    have herror := SparseBernoulli.filtered_error p hp (by norm_num : 2 ≤ 4) C e (hself e)
    have hN : (C e).card*(p:ℝ)^2 ≤ (N:ℝ)*(p:ℝ)^2 :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hC e)) (sq_nonneg (p:ℝ))
    have heq : (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => e∈FiniteLaw.selected C ω)-(p:ℝ)/2 =
      ((SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => e∈FiniteLaw.selected C ω)-(p:ℝ))/2 := by ring
    rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [herror,hN,hnonneg]
  · rw [ite_eq_right he, abs_of_nonneg (by linarith only [(hqq e).1])]
    nlinarith only [(hqq e).2,hN0]

end MetricKMedian.SparsePhysicalBatch

end OAI
