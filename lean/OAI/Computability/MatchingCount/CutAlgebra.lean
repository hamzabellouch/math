import OAI.Computability.MatchingCount.UnitFlow

namespace OAI

section

namespace BinaryMatching.CutAlgebra
open Finset UnitFlow
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

abbrev cross (S : Finset V) (i j : V) : Prop := i∈S ∧ j∉S

lemma cutCapacity_eq (c : V → V → ℕ) (S : Finset V) :
    cutCapacity c S = ∑ i, ∑ j, if cross S i j then c i j else 0 := by
  simp only [cutCapacity,cross,ite_and]
  simp [Finset.sum_ite_irrel]
  apply sum_congr rfl; intro i hi
  have hSc : Sᶜ = univ.filter (fun j => j∉S) := by ext j; simp
  rw [hSc,sum_filter]
  simp

lemma cut_compl (c : V → V → ℕ) (hc : ∀ i j, c i j=c j i) (S : Finset V) :
    cutCapacity c Sᶜ = cutCapacity c S := by
  rw [cutCapacity_eq,cutCapacity_eq,sum_comm]
  apply sum_congr rfl; intro i hi
  apply sum_congr rfl; intro j hj
  simp only [cross,mem_compl,not_not]
  rw [hc j i]
  by_cases his : i∈S <;> by_cases hjs : j∈S <;> simp [his,hjs]

lemma cut_submodular (c : V → V → ℕ) (S A : Finset V) :
    cutCapacity c (S∩A) + cutCapacity c (S∪A) ≤ cutCapacity c S + cutCapacity c A := by
  simp only [cutCapacity_eq,← sum_add_distrib]
  apply sum_le_sum; intro i hi
  apply sum_le_sum; intro j hj
  by_cases his : i∈S <;> by_cases hia : i∈A <;>
    by_cases hjs : j∈S <;> by_cases hja : j∈A <;>
    simp [cross,his,hia,hjs,hja]

def push (c : V → V → ℕ) (f : V → W) (i j : W) : ℕ :=
  if i=j then 0 else ∑ u, ∑ v, if f u=i ∧ f v=j then c u v else 0

def lift (f : V → W) (T : Finset W) : Finset V := univ.filter (fun v => f v∈T)

omit [DecidableEq V] [Fintype W] in
lemma mem_lift (f : V → W) (T : Finset W) (v : V) : v∈lift f T ↔ f v∈T := by
  simp [lift]

omit [DecidableEq V] [Fintype W] in
lemma push_symm (c : V → V → ℕ) (hc : ∀ i j, c i j=c j i) (f : V → W) :
    ∀ i j, push c f i j=push c f j i := by
  intro i j
  by_cases hij : i=j
  · subst j; rfl
  simp only [push,ite_eq_right hij,ite_eq_right (Ne.symm hij)]
  rw [sum_comm]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  rw [hc v u]
  simp only [and_comm]

omit [DecidableEq V] [Fintype W] in
lemma push_diag (c : V → V → ℕ) (f : V → W) (i : W) : push c f i i=0 := by
  simp [push]

omit [DecidableEq V] [DecidableEq W] in
lemma sum_four_swap (h : W → W → V → V → ℕ) :
    (∑ i, ∑ j, ∑ u, ∑ v, h i j u v) = ∑ u, ∑ v, ∑ i, ∑ j, h i j u v := by
  calc
    _ = ∑ i, ∑ u, ∑ j, ∑ v, h i j u v := by
      apply sum_congr rfl; intro i hi
      rw [sum_comm]
    _ = ∑ u, ∑ i, ∑ j, ∑ v, h i j u v := by rw [sum_comm]
    _ = ∑ u, ∑ i, ∑ v, ∑ j, h i j u v := by
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro i hi
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl; intro u hu
      rw [sum_comm]

lemma cut_push (c : V → V → ℕ) (f : V → W) (T : Finset W) :
    cutCapacity (push c f) T = cutCapacity c (lift f T) := by
  rw [cutCapacity_eq,cutCapacity_eq]
  have he : ∀ i j, (if cross T i j then push c f i j else 0) =
      ∑ u, ∑ v, if cross T (f u) (f v) ∧ f u=i ∧ f v=j then c u v else 0 := by
    intro i j
    by_cases hh : cross T i j
    · have hij : i≠j := by intro h; subst j; exact hh.2 hh.1
      simp only [ite_eq_left hh,push,ite_eq_right hij]
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro v hv
      by_cases hui : f u=i <;> by_cases hvj : f v=j <;> simp_all
    · simp only [ite_eq_right hh]
      symm
      apply sum_eq_zero; intro u hu
      apply sum_eq_zero; intro v hv
      by_cases hui : f u=i <;> by_cases hvj : f v=j <;> simp_all
  simp_rw [he]
  rw [sum_four_swap]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  simp only [cross,mem_lift]
  by_cases hh : f u∈T ∧ f v∉T
  · simp only [hh,true_and]
    simp [ite_and,Finset.sum_ite_irrel,eq_comm]
  · simp [hh]

omit [DecidableEq V] in

lemma push_total_le (c : V → V → ℕ) (f : V → W) :
    (∑ i, ∑ j, push c f i j) ≤ ∑ u, ∑ v, c u v := by
  calc
    _ ≤ ∑ i, ∑ j, ∑ u, ∑ v, if f u=i ∧ f v=j then c u v else 0 := by
      apply sum_le_sum; intro i hi
      apply sum_le_sum; intro j hj
      simp only [push]
      split_ifs <;> omega
    _ = _ := by
      rw [sum_four_swap]
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro v hv
      simp [ite_and,Finset.sum_ite_irrel,eq_comm]

end BinaryMatching.CutAlgebra
end

end OAI
