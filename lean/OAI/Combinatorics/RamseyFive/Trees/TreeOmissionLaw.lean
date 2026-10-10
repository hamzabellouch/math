import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.PivotTree

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree FiniteEntropy
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) [∀a c,Fintype (Ω a c)]
  (M : ∀a c,Ω a c→Type z) (left right : ∀a c t,M a c t→C)
  (enc : ∀a c t,Option (M a c t)) (p : ∀a c,Law (Ω a c))

noncomputable def expectedOmission (b : BinaryTree A) (c : C) : ℝ :=
  ∑ω,tapeLaw Ω p b ω*((b.numNodes:ℝ)-
    (retained Ω M left right b ω c (encoded Ω M left right enc b ω c)).numNodes)

lemma expectedOmission_nonneg (b : BinaryTree A) (c : C) :
    0≤expectedOmission Ω M left right enc p b c := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg ((tapeLaw Ω p b).nonneg ω)
  apply sub_nonneg.mpr
  exact_mod_cast retained_nodes_le Ω M left right b ω c _

lemma expectedOmission_node (a : A) (l r : BinaryTree A) (c : C) :
    expectedOmission Ω M left right enc p (.node a l r) c =
      ∑t,p a c t*((enc a c t).elim ((BinaryTree.node a l r).numNodes:ℝ)
        (fun m=>expectedOmission Ω M left right enc p l (left a c t m)+
          expectedOmission Ω M left right enc p r (right a c t m))) := by
  rw [←piLaw_eval_expectation (p a) c]
  unfold expectedOmission
  simp only [tapeLaw,adaptiveLaw]
  change (∑ω : (∀c,Ω a c) × Tape Ω l × Tape Ω r, _) = _
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  simp only [mul_assoc,←Finset.mul_sum]
  congr 1
  cases he : enc a c (t c) with
  | none =>
    simp only [encoded,he,Option.map_none,retained,Option.elim_none,BinaryTree.numNodes,
      Nat.cast_zero,sub_zero]
    simp only [(tapeLaw Ω p r).sum_one,
      ←Finset.sum_mul,(tapeLaw Ω p l).sum_one,one_mul]
  | some m =>
    simp only [encoded,he,Option.map_some,retained,Option.elim_some,BinaryTree.numNodes,
      Nat.cast_add,Nat.cast_one]
    have hsub (x y u v : ℝ) : x+y+1-(u+v+1)=(x-u)+(y-v) := by ring
    simp only [hsub,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,
      (tapeLaw Ω p l).sum_one,(tapeLaw Ω p r).sum_one,one_mul]
end SharpRamseyFive.TreeCodec

end OAI
