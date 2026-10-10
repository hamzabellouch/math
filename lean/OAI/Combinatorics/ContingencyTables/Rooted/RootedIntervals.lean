import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhysicalCompletion

namespace OAI

/-! # The actual tree intervals for an explicitly selected component root

The maximum-forest cut estimate applies to every reachable root.  Thus
the executed least-root convention retains the same finite tree box,
including for unbalanced retained small-cell views.
-/

namespace ContingencyTables.RootedIntervals

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestCapacity GraphCompletionCounts ForestCut

variable {I J : Type*} [Fintype I] [Fintype J]

lemma nonroot_of_component (A : Instance I J) (S : Selection A.T)
    (u v : I⊕J) (h : A.T.Reachable (S.root u) v) (hv : v≠S.root u) :
    v≠S.root v := by
  have he : S.root v=S.root u := by
    rw [←S.constant h,S.idempotent]
  simpa only [he] using hv

theorem solved_in_intervals (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hsmall : ∀ i j,A.small i j=true →
      (0≤ x i j ∧ x i j≤ A.b i j) ∧ (0≤ q i j ∧ q i j≤ A.b i j))
    (hfree : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) →
      0≤ free i j ∧ free i j≤ A.b i j) :
    ∀ i j,A.T.Adj (.inl i) (.inr j) →
      -((10*A.d*A.b i j:ℕ):ℤ)≤ solved A S x q free i j ∧
        solved A S x q free i j≤(10*A.d*A.b i j:ℕ) := by
  intro i₀ j₀ ht
  let root := S.root (.inl i₀)
  have hb := completion_interval A.small A.b A.T A.hTG A.hT A.hmax i₀ j₀ ht root
    (S.reachable (.inl i₀)).symm
    (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
    (fun i j => (completed A S x q free i j:ℝ)) (fun i j => (A.X i j:ℝ))
    (A.d:ℝ) A.W (by exact_mod_cast A.hd) (by exact_mod_cast A.hcard) A.hlarge
    (by
      intro i j hs
      exact ⟨A.hsmall i j hs,by exact_mod_cast (hsmall i j hs).1,
        by exact_mod_cast (hsmall i j hs).2⟩)
    (by intro i j; exact_mod_cast A.hX i j)
    (by
      intro i j hs htree
      have hn : ¬A.T.Adj (.inl i) (.inr j) := by
        simpa only [treeCell,decide_eq_false_iff_not] using htree
      simp only [completed,hn,ite_false]
      have hf := hfree i j hs hn
      constructor
      · exact_mod_cast hf.1
      · have hcast : (free i j:ℝ)≤(A.b i j:ℝ) := by exact_mod_cast hf.2
        linarith)
    (by
      intro i hcomp hi
      have hrow := row_completed_sum A S x q free i
        (nonroot_of_component A S (.inl i₀) (.inl i) hcomp hi)
      have hrowR : (∑ j,if A.small i j then (x i j:ℝ) else
          (completed A S x q free i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast hrow
      have hXR : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast A.hXr i
      unfold rowDifference
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else
          (completed A S x q free i j:ℝ))-(∑ j,(A.X i j:ℝ)) := by
            rw [←Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> rfl
        _=0 := by rw [hrowR,hXR,sub_self])
    (by
      intro j hcomp hj
      have hcol := column_completed_sum A S x q free j
        (nonroot_of_component A S (.inl i₀) (.inr j) hcomp hj)
      have hcolR : (∑ i,if A.small i j then (q i j:ℝ) else
          (completed A S x q free i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast hcol
      have hXC : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast A.hXc j
      unfold columnDifference
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else
          (completed A S x q free i j:ℝ))-(∑ i,(A.X i j:ℝ)) := by
            rw [←Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> rfl
        _=0 := by rw [hcolR,hXC,sub_self])
  simp only [completed,ht,ite_true] at hb
  constructor
  · have hlow : (-10:ℤ)*(A.d:ℤ)*(A.b i₀ j₀:ℤ)≤ solved A S x q free i₀ j₀ := by
      exact_mod_cast hb.1
    convert hlow using 1
    push_cast
    ring
  · exact_mod_cast hb.2

end ContingencyTables.RootedIntervals

end OAI
