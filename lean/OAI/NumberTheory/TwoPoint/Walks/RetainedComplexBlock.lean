import OAI.NumberTheory.TwoPoint.Walks.RetainedGraphOrientation
import OAI.NumberTheory.TwoPoint.Walks.RetainedActiveEdges
import OAI.NumberTheory.TwoPoint.Walks.BlockFormPrefixBound

namespace OAI

/-! Directed complex correlations as actual overlapping graph blocks. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def retainedComplexPrimeEdge {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) : ℂ :=
  if gate (∏ j, (e.1 j).val) n m ∧ keep n ∧ keep m then
    F n * G m * (retainedRealEdge Q u (eligible (∏ j, (e.1 j).val))
      (actualPaddingVertex Qp) (centeredTuple (∏ j, (e.1 j).val).primeFactors)
      L K (extra (∏ j, (e.1 j).val))
      (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L z) h (∏ j, (e.1 j).val) e.2.val n m : ℂ)
  else 0

lemma retainedComplexPrimeEdge_support {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ)
    (hm : m ≠ n + retainedPrimeStep eligible h e) :
    retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n m = 0 := by
  unfold retainedComplexPrimeEdge
  split_ifs
  · by_cases he : eligible (∏ j, (e.1 j).val) e.2.val
    · rw [retainedPrimeStep, ite_eq_left he] at hm
      rw [retainedRealEdge_support _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm]
      simp
    · simp [retainedRealEdge, he]
  · rfl

noncomputable def retainedComplexBlock {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (t : ℕ) : ℂ :=
  let site := fun i : Fin M => (i.val : ℤ) + (t + 2 : ℕ)
  let A := retainedPrimeMatrix P site Q u eligible (actualPaddingVertex Qp) L K extra
    (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
      actualPaddingDegreeCut Qp L z) h
    (fun d i j => gate d (site i) (site j) ∧ keep (site i) ∧ keep (site j))
  ∑ i, ∑ j, F (site i) * G (site j) * A i j

lemma retainedComplexBlock_eq_edges {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (t : ℕ) :
    retainedComplexBlock P M Q Qp u eligible L K W extra h gate keep F G t =
      ∑ e : ((j : Fin J) → P j) × Q, ∑ i : Fin M, ∑ j : Fin M,
        retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e
          ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ)) := by
  dsimp only [retainedComplexBlock]
  simp only [retainedPrimeMatrix, Matrix.sum_apply, mul_sum]
  have hs := sum_gated_edges (D := (j : Fin J) → P j) (V := Fin M) Q
    (fun d i j => gate (∏ k, (d k).val) ((i.val : ℤ) + (t + 2 : ℕ))
      ((j.val : ℤ) + (t + 2 : ℕ)) ∧ keep ((i.val : ℤ) + (t + 2 : ℕ)) ∧
      keep ((j.val : ℤ) + (t + 2 : ℕ)))
    (fun d q i j => F ((i.val : ℤ) + (t + 2 : ℕ)) * G ((j.val : ℤ) + (t + 2 : ℕ)) *
      (retainedRealEdge Q u (eligible (∏ k, (d k).val)) (actualPaddingVertex Qp)
        (centeredTuple (∏ k, (d k).val).primeFactors) L K (extra (∏ k, (d k).val))
        (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
          actualPaddingDegreeCut Qp L z) h (∏ k, (d k).val) q
        ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ)) : ℂ))
  refine Eq.trans ?_ (hs.trans ?_)
  · calc
      _ = ∑ i : Fin M, ∑ d : (j : Fin J) → P j, ∑ j : Fin M,
          F ((i.val : ℤ) + (t + 2 : ℕ)) * G ((j.val : ℤ) + (t + 2 : ℕ)) *
            retainedDirectedMatrix (fun i : Fin M => (i.val : ℤ) + (t + 2 : ℕ)) Q u
              (eligible (∏ k, (d k).val)) (actualPaddingVertex Qp)
              (centeredTuple (∏ k, (d k).val).primeFactors) L K
              (extra (∏ k, (d k).val))
              (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
                actualPaddingDegreeCut Qp L z) h (∏ k, (d k).val)
              (fun i j => gate (∏ k, (d k).val) ((i.val : ℤ) + (t + 2 : ℕ))
                ((j.val : ℤ) + (t + 2 : ℕ)) ∧ keep ((i.val : ℤ) + (t + 2 : ℕ)) ∧
                  keep ((j.val : ℤ) + (t + 2 : ℕ))) i j := by
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        unfold retainedDirectedMatrix
        split_ifs <;> simp only [mul_sum, mul_zero]
  · apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    unfold retainedComplexPrimeEdge
    by_cases he : gate (∏ k, (e.1 k).val) ((i.val : ℤ) + (t + 2 : ℕ))
      ((j.val : ℤ) + (t + 2 : ℕ)) ∧ keep ((i.val : ℤ) + (t + 2 : ℕ)) ∧
        keep ((j.val : ℤ) + (t + 2 : ℕ))
    · simp only [he]
    · simp only [he, ite_false]


lemma retainedComplexBlock_eq_blocks {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (t : ℕ) :
    retainedComplexBlock P M Q Qp u eligible L K W extra h gate keep F G t =
      edgeBlockSum univ (retainedPrimeStep eligible h)
        (fun e n => retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
          ((n : ℤ) + retainedPrimeStep eligible h e)) M t := by
  rw [retainedComplexBlock_eq_edges]
  exact directed_block_form_eq _ _ (retainedComplexPrimeEdge_support P Q Qp u eligible
    L K W extra h gate keep F G) M t

/-- The prefix transfer is valid for arbitrary complex factors. The row and block bounds
are separate estimates, so no positivity of either factor is required. -/
theorem retainedComplexBlock_prefix_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (M R N : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (hM : 0 < M) (hN : 0 < N) (B C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ e : ((j : Fin J) → P j) × Q, retainedPrimeStep eligible h e ≤ R)
    (hrow : ∀ n : ℕ, 0 < n →
      (∑ e : ((j : Fin J) → P j) × Q,
        ‖retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
          ((n : ℤ) + retainedPrimeStep eligible h e)‖) ≤ C)
    (havg : uniformAverage (fun t : Fin N =>
      ‖retainedComplexBlock P M Q Qp u eligible L K W extra h gate keep F G t.val‖) ≤ B) :
    ‖positivePrefix (fun n => ∑ e : ((j : Fin J) → P j) × Q,
      retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
        ((n : ℤ) + retainedPrimeStep eligible h e)) N / (N : ℂ)‖ ≤
      B / M + (R : ℝ) / M * C + 2 * (M : ℝ) / N * C := by
  have hb := block_form_prefix_bound (retainedPrimeStep eligible h)
    (fun e n => retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
      ((n : ℤ) + retainedPrimeStep eligible h e))
    (retainedComplexBlock P M Q Qp u eligible L K W extra h gate keep F G) M R N
    hM hN (1 / 2) B C (by norm_num) hC hr hrow
    (fun t => by
      simpa using (retainedComplexBlock_eq_blocks P M Q Qp u eligible L K W extra
        h gate keep F G t)) havg
  norm_num at hb ⊢
  exact hb

end TwoPointCorrelations

end OAI
