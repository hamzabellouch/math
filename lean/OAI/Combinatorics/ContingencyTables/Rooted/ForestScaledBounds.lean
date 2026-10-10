import OAI.Combinatorics.ContingencyTables.Rooted.ForestScaledIdentification

namespace OAI

/-! # The actual continuous forest penalty stays within the source allowance -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty
open ForestCountIdentification BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rowCounts (A : Instance I J) (z : View A → ℕ) : I → J → ℤ :=
  fun i j => (smallX A.small z i j:ℤ)

noncomputable def columnCounts (A : Instance I J) (z : View A → ℕ) : I → J → ℤ :=
  fun i j => ((A.b i j-smallY A.small z i j:ℕ):ℤ)

lemma rowCounts_bounds (A : Instance I J) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (i : I) (j : J) (hs : A.small i j=true) :
    0 ≤ rowCounts A z i j ∧ rowCounts A z i j ≤ A.b i j := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  have hh : smallX A.small z i j ≤ A.b i j := by
    simpa only [smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
  change (smallX A.small z i j:ℤ) ≤ (A.b i j:ℤ)
  exact_mod_cast hh

lemma columnCounts_bounds (A : Instance I J) (z : View A → ℕ) (i : I) (j : J) :
    0 ≤ columnCounts A z i j ∧ columnCounts A z i j ≤ A.b i j := by
  unfold columnCounts
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast Nat.sub_le (A.b i j) (smallY A.small z i j)⟩

lemma rootConstant_bound (A : Instance I J) (z : View A → ℕ) (hz : InBox (bounds A) z) :
    rootConstant A (rowCounts A z) (columnCounts A z) ≤ 2*(A.d:ℝ)*A.W := by
  have hroot := root_eq_large A.small A.b A.T A.hTG A.hT A.hmax
    (fun i j hs => (A.hlarge i j hs).2)
  have hh := sum_abs_signedResidual_le A.small A.T A.hTG A.b A.r A.c
    (rowCounts A z) (columnCounts A z) 0 A.X A.hXr A.hXc hroot
    (rowCounts_bounds A z hz) (fun i j _ => columnCounts_bounds A z i j) A.hX
  have hsmall : (∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0) ≤ (A.d:ℝ)*A.W := by
    calc
      _ ≤ ∑ _i : I,∑ _j : J,(A.W:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        cases hs : A.small i j
        · simp only [Bool.false_eq_true,ite_false]
          positivity
        · simp only [ite_true]
          exact_mod_cast (A.hsmall i j hs).le
      _ = (Fintype.card I*Fintype.card J:ℕ)*(A.W:ℝ) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast A.hcard) (Nat.cast_nonneg _)
  unfold rootConstant
  calc
    _ ≤ ∑ a,|(signedResidual A.small A.T A.r A.c (rowCounts A z) (columnCounts A z) 0 a:ℝ)| := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs <;> first | exact le_rfl | exact abs_nonneg _
    _ ≤ _ := hh.trans (by linarith)

noncomputable def zeroAssignment (A : Instance I J) : FreeIndex A.small A.T A.b :=
  fun _ => ⟨0,Nat.succ_pos _⟩

lemma integerCube_zero (A : Instance I J) (B : ℝ) : integerCube A B (zeroAssignment A)=0 := by
  funext a
  simp only [integerCube,zeroAssignment,Nat.cast_zero,mul_zero,zero_div,Pi.zero_apply]

lemma zero_tree_bound (A : Instance I J) (B : ℝ) (hB : 0 < B)
    (z : View A → ℕ) (hz : InBox (bounds A) z) (t : TreeCell A.T) :
    intervalCost (scaledTree A B (rowCounts A z) (columnCounts A z) 0 t) ≤ 10*(A.d:ℝ) := by
  have hzero : (fun i j => (freeTable A.small A.T A.b (zeroAssignment A) i j:ℤ))=0 := by
    funext i j
    unfold freeTable zeroAssignment
    split_ifs <;> rfl
  have hinterval := solved_in_intervals A.small A.b A.T A.hTG A.hT A.hmax A.r A.c
    (rowCounts A z) (columnCounts A z) 0 A.X A.d A.W A.hd A.hcard A.hlarge
    (by
      intro i j hs
      exact ⟨A.hsmall i j hs,rowCounts_bounds A z hz i j hs,columnCounts_bounds A z i j⟩)
    (by intro i j _ _; exact ⟨le_rfl,Nat.cast_nonneg _⟩) A.hX A.hXr A.hXc
    t.val.1 t.val.2 t.property
  rw [← integerCube_zero A B,scaledTree_integer A B hB,hzero,intervalCost_div]
  · have hb : (0:ℝ) < A.b t.val.1 t.val.2 := by exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
    rw [div_le_iff₀ hb]
    have hlo : -(10*(A.d:ℝ)*A.b t.val.1 t.val.2) ≤
        (solved A.small A.T A.r A.c (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ) := by
      exact_mod_cast hinterval.1
    have hup : (solved A.small A.T A.r A.c (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ) ≤
        10*(A.d:ℝ)*A.b t.val.1 t.val.2 := by exact_mod_cast hinterval.2
    apply max_le
    · positivity
    · apply max_le <;> linarith
  · exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2

/-- The 1/8 local change bound and the actual baseline root/tree bounds
give D(v)≤H throughout the entire continuous bin cube, including its
boundary and the empty free-coordinate case. -/
theorem penalty_cube_bound (A : Instance I J) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 < B)
    (z : View A → ℕ) (hz : InBox (bounds A) z)
    (v : FreeCell A.small A.T → ℝ) (hv : ∀ f,0 ≤ v f ∧ v f ≤ B) :
    0 ≤ penalty A C B (rowCounts A z) (columnCounts A z) v ∧
      penalty A C B (rowCounts A z) (columnCounts A z) v ≤ C*(10*(A.d:ℝ)^2*((A.W:ℝ)+1)) := by
  have hzero : penalty A C B (rowCounts A z) (columnCounts A z) 0 ≤
      C*(2*(A.d:ℝ)*A.W+10*(A.d:ℝ)^2) := by
    unfold penalty
    apply mul_le_mul_of_nonneg_left _ hC
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => zero_tree_bound A B hB z hz t)
    have ht : (∑ t : TreeCell A.T,intervalCost (scaledTree A B (rowCounts A z) (columnCounts A z) 0 t)) ≤
        10*(A.d:ℝ)^2 := by
      calc
        _ ≤ (Fintype.card (TreeCell A.T):ℝ)*(10*(A.d:ℝ)) := by simpa using hsum
        _ ≤ (A.d:ℝ)*(10*(A.d:ℝ)) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast tree_card_le A) (by positivity)
        _ = _ := by ring
    linarith [rootConstant_bound A z hz]
  have hchange := (le_abs_self _).trans (penalty_change A C B hC hB
    (rowCounts A z) (columnCounts A z) v 0 B hB.le (by
      intro f
      simpa only [Pi.zero_apply,sub_zero,abs_of_nonneg (hv f).1] using (hv f).2))
  have hcancel : (2*C*(A.d:ℝ)^2/B)*B=2*C*(A.d:ℝ)^2 := div_mul_cancel₀ _ hB.ne'
  rw [hcancel] at hchange
  have hd : (1:ℝ) ≤ A.d := by exact_mod_cast A.hd
  have hW : (2:ℝ) ≤ A.W := by exact_mod_cast A.hW
  have hscalar : 2*(A.d:ℝ)*A.W+12*(A.d:ℝ)^2 ≤ 10*(A.d:ℝ)^2*((A.W:ℝ)+1) := by
    have hdd : (A.d:ℝ) ≤ (A.d:ℝ)^2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hdd (by positivity : (0:ℝ) ≤ A.W)
    have hprod' := mul_le_mul_of_nonneg_left hW (sq_nonneg (A.d:ℝ))
    nlinarith
  refine ⟨penalty_nonnegative A C B hC _ _ v,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hscalar hC]

end ContingencyTables.ForestScaledPenalty

end OAI
