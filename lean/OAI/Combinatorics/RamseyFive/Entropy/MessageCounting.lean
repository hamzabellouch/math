import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.TreeWeights

namespace OAI

namespace SharpRamseyFive.MessageWeights
open FiniteEntropy
open scoped Classical BigOperators
universe u
variable {A : Type u} [Fintype A]
lemma card_le_exp (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1)
    (S : Finset A) (B : ℝ) (hS : ∀a∈S,c a≤B) : (S.card:ℝ)≤Real.exp B := by
  have hs : (S.card:ℝ)*Real.exp (-B)≤1 := calc
    _ = ∑a∈S,Real.exp (-B) := by simp
    _ ≤ ∑a∈S,Real.exp (-c a) := Finset.sum_le_sum (fun a ha=>Real.exp_le_exp.mpr (neg_le_neg (hS a ha)))
    _ ≤ ∑a,Real.exp (-c a) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _=>(Real.exp_pos _).le)
    _ ≤ 1 := hc
  have h := mul_le_mul_of_nonneg_right hs (Real.exp_pos B).le
  simpa only [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] using h

lemma entropy_le_cost (p : Law A) (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1) :
    entropy p≤∑a,p a*c a := by
  have hh := entropy_le_cross_subprob p (fun a=>Real.exp (-c a))
    (fun _=>Real.exp_pos _) hc
  simpa only [Real.log_exp,mul_neg,Finset.sum_neg_distrib,neg_neg] using hh
lemma entropy_le_bound (p : Law A) (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1)
    (B : ℝ) (hB : ∀a,0<p a→c a≤B) : entropy p≤B := by
  apply (entropy_le_cost p c hc).trans
  calc
    _ ≤ ∑a,p a*B := Finset.sum_le_sum (fun a _=>by
      by_cases hp : p a=0
      · simp [hp]
      · exact mul_le_mul_of_nonneg_left (hB a (lt_of_le_of_ne (p.nonneg _) (Ne.symm hp))) (p.nonneg a))
    _ = B := by rw [←Finset.sum_mul,p.sum_one,one_mul]
lemma entropy_map_le_bound {J : Type*} [Fintype J] (p : Law J) (e : J→A)
    (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1) (B : ℝ)
    (hb : ∀j,c (e j)≤B) : entropy (map p e)≤B := by
  apply (entropy_le_cost (map p e) c hc).trans
  rw [sum_map]
  calc
    _ ≤ ∑j,p j*B := Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hb j) (p.nonneg j))
    _ = B := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.MessageWeights
namespace SharpRamseyFive.TreeCodec
open BinaryTree MessageWeights
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)
omit [Fintype C] in
lemma slotCost_le_original (lc : ∀a c t,M a c t→ℝ)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) (m : Message Ω M left right b ω c) :
    slotCost Ω M left right lc b ω c m≤cost Ω M left right lc b ω c m+
      (2*(b.numNodes:ℝ)+1)*Real.log 2 := by
  have hn : ((retained Ω M left right b ω c m).numNodes:ℝ)≤b.numNodes := by
    exact_mod_cast retained_nodes_le Ω M left right b ω c m
  have hh := mul_le_mul_of_nonneg_right (show 2*((retained Ω M left right b ω c m).numNodes:ℝ)+1≤2*(b.numNodes:ℝ)+1 by linarith)
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  have hl := slotCost_le Ω M left right lc b ω c m
  linarith only [hl,hh]
end SharpRamseyFive.TreeCodec

end OAI
