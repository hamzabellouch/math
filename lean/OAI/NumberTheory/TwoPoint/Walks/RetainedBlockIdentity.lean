import OAI.NumberTheory.TwoPoint.Bounds.ProjectedPrimeLiouville
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionCompressionGate
import OAI.NumberTheory.TwoPoint.Walks.BlockEdgeForm

namespace OAI

/-! The actual projected block form is the sum of its ambient directed
edges.  The identity includes every vertex deletion, so overlapping blocks
can be compared directly with a prefix of the retained correlation. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma sum_gated_edges {D V : Type*} [Fintype D] [Fintype V]
    (Q : Finset ℕ) (gate : D → V → V → Prop) (F : D → ℕ → V → V → ℂ) :
    (∑ d : D, ∑ i : V, ∑ j : V, if gate d i j then ∑ q ∈ Q, F d q i j else 0) =
      ∑ e : D × Q, ∑ i : V, ∑ j : V, if gate e.1 i j then F e.1 e.2.val i j else 0 := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro d _
  calc
    _ = ∑ i : V, ∑ j : V, ∑ q : Q, if gate d i j then F d q.val i j else 0 := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hg : gate d i j
      · simp only [hg, ite_true]
        exact (sum_coe_sort Q (fun q => F d q i j)).symm
      · simp only [hg, ite_false, sum_const_zero]
    _ = ∑ i : V, ∑ q : Q, ∑ j : V, if gate d i j then F d q.val i j else 0 := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := sum_comm

noncomputable def retainedPrimeEdge {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) : ℂ :=
  if gate (∏ j, (e.1 j).val) n m ∧ keep n ∧ keep m then
    retainedLiouvilleEdge Q u (eligible (∏ j, (e.1 j).val)) (actualPaddingVertex Qp)
      (centeredTuple (∏ j, (e.1 j).val).primeFactors) L K (extra (∏ j, (e.1 j).val))
      (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L z) h (∏ j, (e.1 j).val) e.2.val n m
  else 0

lemma retainedPrimeEdge_support {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ)
    (hm : m ≠ n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ)) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m = 0 := by
  unfold retainedPrimeEdge
  split_ifs
  · exact retainedLiouvilleEdge_support _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm
  · rfl

theorem primeBlockCompression_retained_identity {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (c : ℤ) :
    let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) integerLiouville
    inner ℂ v (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp)
      L K W extra h (fun d n m => gate d (n + c) (m + c)) keep c v) =
      (2 * (L : ℂ)) * ∑ e : ((j : Fin J) → P j) × Q, ∑ i : Fin M, ∑ j : Fin M,
        retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e
          ((i.val : ℤ) + c) ((j.val : ℤ) + c) := by
  dsimp only
  have hg : ∀ d (i j : Fin M),
      (gate d ((i.val : ℤ) + c) ((j.val : ℤ) + c) ∧
        keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c)) ↔
      (gate d ((j.val : ℤ) + c) ((i.val : ℤ) + c) ∧
        keep ((j.val : ℤ) + c) ∧ keep ((i.val : ℤ) + c)) := by
    intro d i j
    rw [hgate]
    tauto
  have hi := projected_prime_liouville_quadratic P hprime hdisjoint
    (fun i : Fin M => (i.val : ℤ) + c) Q Qp u eligible L K W extra h
    (fun d i j => gate d ((i.val : ℤ) + c) ((j.val : ℤ) + c) ∧
      keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c)) hg
  dsimp only at hi
  rw [primeBlockCompression]
  rw [hi]
  congr 1
  have hs := sum_gated_edges (D := (j : Fin J) → P j) (V := Fin M) Q
    (fun d i j => gate (∏ k, (d k).val) ((i.val : ℤ) + c) ((j.val : ℤ) + c) ∧
      keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c))
    (fun d q i j => retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val))
      (actualPaddingVertex Qp) (centeredTuple (∏ k, (d k).val).primeFactors) L K
      (extra (∏ k, (d k).val))
      (fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L n) h (∏ k, (d k).val) q
      ((i.val : ℤ) + c) ((j.val : ℤ) + c))
  refine hs.trans ?_
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  unfold retainedPrimeEdge
  split_ifs <;> rfl

theorem primeBlockCompression_retained_blocks {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M t : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) :
    let c : ℤ := (t + 2 : ℕ)
    let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) integerLiouville
    inner ℂ v (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp)
      L K W extra h (fun d n m => gate d (n + c) (m + c)) keep c v) =
      (2 * (L : ℂ)) * edgeBlockSum univ
        (fun e : ((j : Fin J) → P j) × Q => h * e.2.val * ∏ j, (e.1 j).val)
        (fun e n => retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
          ((n : ℤ) + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) M t := by
  dsimp only
  rw [primeBlockCompression_retained_identity P hprime hdisjoint M Q Qp u eligible
    L K W extra h gate hgate keep]
  rw [directed_block_form_eq _ _ (retainedPrimeEdge_support P Q Qp u eligible
    L K W extra h gate keep)]

end TwoPointCorrelations

end OAI
