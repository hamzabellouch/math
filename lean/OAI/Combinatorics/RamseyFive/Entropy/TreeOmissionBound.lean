import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeOmissionLaw

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree FiniteEntropy
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) [∀a c,Fintype (Ω a c)]
  (M : ∀a c,Ω a c→Type z) (left right : ∀a c t,M a c t→C)
  (enc : ∀a c t,Option (M a c t)) (p : ∀a c,Law (Ω a c))

def omissionBudget (e : A→ℝ) : BinaryTree A→ℝ
  | .nil => 0
  | .node a l r => e a*(BinaryTree.node a l r).numNodes+
      omissionBudget e l+omissionBudget e r

lemma omissionBudget_nonneg (e : A→ℝ) (he : ∀a,0≤e a) (b : BinaryTree A) :
    0≤omissionBudget e b := by
  induction b with
  | nil => simp [omissionBudget]
  | node a l r hl hr => exact add_nonneg (add_nonneg (mul_nonneg (he a) (by positivity)) hl) hr

lemma expectedOmission_le (e : A→ℝ) (he : ∀a,0≤e a)
    (hfail : ∀a c, (∑t,p a c t*(if enc a c t=none then (1:ℝ) else 0))≤e a)
    (b : BinaryTree A) (c : C) :
    expectedOmission Ω M left right enc p b c≤omissionBudget e b := by
  induction b generalizing c with
  | nil => simp [expectedOmission,retained,BinaryTree.numNodes,omissionBudget]
  | node a l r hl hr =>
    rw [expectedOmission_node]
    have hsum : (∑t,p a c t*((enc a c t).elim ((BinaryTree.node a l r).numNodes:ℝ)
        (fun m=>expectedOmission Ω M left right enc p l (left a c t m)+
          expectedOmission Ω M left right enc p r (right a c t m)))) ≤
        ∑t,p a c t*((if enc a c t=none then (1:ℝ) else 0)*(BinaryTree.node a l r).numNodes+
          omissionBudget e l+omissionBudget e r) := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ ((p a c).nonneg t)
      cases hh : enc a c t with
      | none =>
        simp only [Option.elim_none,ite_true,one_mul]
        have h1 := omissionBudget_nonneg e he l
        have h2 := omissionBudget_nonneg e he r
        linarith
      | some m =>
        simp only [Option.elim_some,Option.some_ne_none,ite_false,zero_mul,zero_add]
        exact add_le_add (hl _) (hr _)
    calc
      _ ≤ _ := hsum
      _ = (∑t,p a c t*(if enc a c t=none then (1:ℝ) else 0))*(BinaryTree.node a l r).numNodes+
          omissionBudget e l+omissionBudget e r := by
        simp only [mul_add,Finset.sum_add_distrib,←mul_assoc,←Finset.sum_mul,(p a c).sum_one,one_mul]
      _ ≤ omissionBudget e (.node a l r) := by
        have hh := mul_le_mul_of_nonneg_right (hfail a c) (Nat.cast_nonneg (α:=ℝ) ((BinaryTree.node a l r).numNodes))
        change _ ≤ e a*((BinaryTree.node a l r).numNodes:ℝ)+omissionBudget e l+omissionBudget e r
        linarith
end SharpRamseyFive.TreeCodec

end OAI
