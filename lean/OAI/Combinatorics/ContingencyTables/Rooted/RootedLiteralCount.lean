import OAI.Combinatorics.ContingencyTables.Rooted.RootedPenalty
import OAI.Combinatorics.ContingencyTables.Rooted.RootedIntervals

namespace OAI

/-! # Multiplicity-one physical tree sum with the executed root convention -/

namespace ContingencyTables.RootedLiteralCount

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open RootedPenalty ForestLiteralCount GraphCompletionCounts
open ForestPhysicalCompletion (rowResidual columnResidual)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def actualPenalty (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (tree : I → J → ℤ) : ℝ :=
  (∑ v,if rootFlag S v then
    |actualDeviation A.small A.T A.b x y free A.r A.c tree v| else 0)+
  ∑ i,∑ j,if A.T.Adj (.inl i) (.inr j) then
    max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-A.b i j))/(A.b i j:ℝ) else 0

def RootConditions (A : Instance I J) (S : Selection A.T)
    (x q free tree : I → J → ℤ) : Prop :=
  (∀ i,Sum.inl i≠S.root (.inl i) →
    (∑ j,tree i j)=rowResidual A.small A.T A.r x free i) ∧
  (∀ j,Sum.inr j≠S.root (.inr j) →
    (∑ i,tree i j)=columnResidual A.small A.T A.c q free j)

lemma penalty_profile (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (a : TreeIndex A.T A.d A.b)
    (hy : ∀ i j,A.small i j=true → y i j≤ A.b i j)
    (hf : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) → free i j≤ A.b i j) :
    penalty A S (profile A.small A.T A.d A.b x y free a)=
      actualPenalty A S x y free (physical A.T A.d A.b a) := by
  unfold penalty rootPenalty actualPenalty
  rw [show ForestPenaltyApplication.deviation (ell A) (widths A) A.r A.c
      (profile A.small A.T A.d A.b x y free a)=
      actualDeviation A.small A.T A.b x y free A.r A.c (physical A.T A.d A.b a) from
    deviation_profile A.small A.T A.hTG A.d A.b x y free a A.r A.c hy hf]
  congr 1
  unfold ForestPenaltyApplication.treePenalty
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases ht : A.T.Adj (.inl i) (.inr j)
  · have hs : A.small i j=false := A.hTG ht
    have hrow := row_profile A.small A.T A.hTG A.d A.b x y free a i j
    simp only [hs,Bool.false_eq_true,ite_false,largeValue,ht,ite_true] at hrow
    simp only [ht,ite_true,EqualitySoftening.affineDistance,mul_one]
    rw [show (ell A i j:ℝ)+(profile A.small A.T A.d A.b x y free a ((i,j),false):ℝ)=
      (physical A.T A.d A.b a i j:ℝ) from hrow]
  · simp only [ht,ite_false]

lemma nonroot_iff (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (tree : I → J → ℤ)
    (hsupport : ∀ i j,¬A.T.Adj (.inl i) (.inr j) → tree i j=0) :
    (∀ g,rootFlag S g=false →
      actualDeviation A.small A.T A.b x y free A.r A.c tree g=0) ↔
    RootConditions A S (fun i j => (x i j:ℤ))
      (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ)) tree := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hflag : rootFlag S (.inl i)=false := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hi
      have hraw := h (.inl i) hflag
      simp only [actualDeviation,Sum.elim_inl] at hraw
      have hsum : (∑ j,if A.small i j then (x i j:ℤ) else largeValue A.T tree free i j)=A.r i :=
        by exact_mod_cast sub_eq_zero.mp hraw
      simp_rw [ForestLiteralCount.row_pointwise A.small A.T A.hTG x free tree hsupport] at hsum
      rw [Finset.sum_add_distrib] at hsum
      unfold rowResidual
      omega
    · intro j hj
      have hflag : rootFlag S (.inr j)=false := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hj
      have hraw := h (.inr j) hflag
      simp only [actualDeviation,Sum.elim_inr] at hraw
      have hsum : (∑ i,if A.small i j then ((A.b i j-y i j:ℕ):ℤ)
          else largeValue A.T tree free i j)=A.c j := by exact_mod_cast sub_eq_zero.mp hraw
      simp_rw [ForestLiteralCount.column_pointwise A.small A.T A.hTG A.b y free tree hsupport] at hsum
      rw [Finset.sum_add_distrib] at hsum
      unfold columnResidual
      omega
  · intro h g hg
    cases g with
    | inl i =>
      have hi : Sum.inl i≠S.root (.inl i) := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hg
      have hsum : (∑ j,if A.small i j then (x i j:ℤ) else largeValue A.T tree free i j)=A.r i := by
        simp_rw [ForestLiteralCount.row_pointwise A.small A.T A.hTG x free tree hsupport]
        rw [Finset.sum_add_distrib,h.1 i hi]
        exact sub_add_cancel _ _
      simp only [actualDeviation,Sum.elim_inl]
      have hreal : (((∑ j,if A.small i j then (x i j:ℤ)
        else largeValue A.T tree free i j):ℤ):ℝ)=(A.r i:ℝ) := by exact_mod_cast hsum
      rw [hreal,sub_self]
    | inr j =>
      have hj : Sum.inr j≠S.root (.inr j) := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hg
      have hsum : (∑ i,if A.small i j then ((A.b i j-y i j:ℕ):ℤ)
          else largeValue A.T tree free i j)=A.c j := by
        simp_rw [ForestLiteralCount.column_pointwise A.small A.T A.hTG A.b y free tree hsupport]
        rw [Finset.sum_add_distrib,h.2 j hj]
        exact sub_add_cancel _ _
      simp only [actualDeviation,Sum.elim_inr]
      have hreal : (((∑ i,if A.small i j then ((A.b i j-y i j:ℕ):ℤ)
        else largeValue A.T tree free i j):ℤ):ℝ)=(A.c j:ℝ) := by exact_mod_cast hsum
      rw [hreal,sub_self]

noncomputable def solutionIndex (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hbox : ∀ i j,A.T.Adj (.inl i) (.inr j) →
      -((10*A.d*A.b i j:ℕ):ℤ)≤ solved A S x q free i j ∧
        solved A S x q free i j≤(10*A.d*A.b i j:ℕ)) : TreeIndex A.T A.d A.b := fun e =>
  ⟨(solved A S x q free e.val.1 e.val.2+(10*A.d*A.b e.val.1 e.val.2:ℕ)).toNat,by
    have h := hbox e.val.1 e.val.2 e.property
    have hz : 0≤ solved A S x q free e.val.1 e.val.2+(10*A.d*A.b e.val.1 e.val.2:ℕ) := by omega
    have hle : (solved A S x q free e.val.1 e.val.2+
        (10*A.d*A.b e.val.1 e.val.2:ℕ)).toNat≤20*A.d*A.b e.val.1 e.val.2 := by
      exact_mod_cast (show ((solved A S x q free e.val.1 e.val.2+
        (10*A.d*A.b e.val.1 e.val.2:ℕ)).toNat:ℤ)≤(20*A.d*A.b e.val.1 e.val.2:ℕ) by
          rw [Int.toNat_of_nonneg hz]
          push_cast at h ⊢
          nlinarith)
    omega⟩

lemma physical_solutionIndex (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hbox : ∀ i j,A.T.Adj (.inl i) (.inr j) →
      -((10*A.d*A.b i j:ℕ):ℤ)≤ solved A S x q free i j ∧
        solved A S x q free i j≤(10*A.d*A.b i j:ℕ)) :
    physical A.T A.d A.b (solutionIndex A S x q free hbox)=solved A S x q free := by
  funext i j
  by_cases h : A.T.Adj (.inl i) (.inr j)
  · have hz : 0≤ solved A S x q free i j+(10*A.d*A.b i j:ℕ) := by
      have hb := hbox i j h
      omega
    simp only [physical,h,dite_eq_left,solutionIndex,Int.toNat_of_nonneg hz]
    omega
  · simp only [physical,h,not_false_eq_true,dite_eq_right,
      solved_supported A S x q free i j h]

theorem tree_indicator_sum (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hsmall : ∀ i j,A.small i j=true →
      (0≤ x i j ∧ x i j≤ A.b i j) ∧ (0≤ q i j ∧ q i j≤ A.b i j))
    (hfree : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) →
      0≤ free i j ∧ free i j≤ A.b i j)
    (weight : (I → J → ℤ) → ℝ) :
    (∑ a : TreeIndex A.T A.d A.b,if RootConditions A S x q free (physical A.T A.d A.b a)
      then weight (physical A.T A.d A.b a) else 0)=weight (solved A S x q free) := by
  let hb := RootedIntervals.solved_in_intervals A S x q free hsmall hfree
  let a₀ := solutionIndex A S x q free hb
  have ha₀ : physical A.T A.d A.b a₀=solved A S x q free := physical_solutionIndex A S x q free hb
  have hsol : RootConditions A S x q free (solved A S x q free) :=
    ⟨table_row A.small A.T S A.hTG _ _,table_column A.small A.T S A.hTG _ _⟩
  rw [Finset.sum_eq_single a₀]
  · simp only [ha₀,hsol,ite_true]
  · intro a _ hne
    by_cases ha : RootConditions A S x q free (physical A.T A.d A.b a)
    · have he := table_unique A.small A.T S A.hTG A.hT _ _ (physical A.T A.d A.b a)
        (physical_supported A.T A.d A.b a) ha.1 ha.2
      have haa : a=a₀ := physical_injective A.T A.d A.b (he.trans ha₀.symm)
      exact (hne haa).elim
    · simp only [ha,ite_false]
  · simp

theorem literal_tree_sum (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (alpha : ℝ)
    (hx : ∀ i j,A.small i j=true → x i j≤ A.b i j)
    (hy : ∀ i j,A.small i j=true → y i j≤ A.b i j)
    (hf : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) → free i j≤ A.b i j) :
    (∑ a : TreeIndex A.T A.d A.b,
      physicalWeight A S alpha (profile A.small A.T A.d A.b x y free a))=
      (2:ℝ)^(-alpha*actualPenalty A S x y free
        (solved A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
          (fun i j => (free i j:ℤ)))) := by
  have hsum := tree_indicator_sum A S (fun i j => (x i j:ℤ))
    (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ))
    (by
      intro i j hs
      refine ⟨⟨Nat.cast_nonneg _,?_⟩,⟨Nat.cast_nonneg _,?_⟩⟩
      · exact_mod_cast hx i j hs
      · exact_mod_cast Nat.sub_le (A.b i j) (y i j))
    (by
      intro i j hs ht
      exact ⟨Nat.cast_nonneg _,by exact_mod_cast hf i j hs ht⟩)
    (fun tree => (2:ℝ)^(-alpha*actualPenalty A S x y free tree))
  calc
    _=(∑ a : TreeIndex A.T A.d A.b,
      if RootConditions A S (fun i j => (x i j:ℤ))
        (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ)) (physical A.T A.d A.b a)
      then (2:ℝ)^(-alpha*actualPenalty A S x y free (physical A.T A.d A.b a)) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [RootedPenalty.exact_eq,
          show ForestPenaltyApplication.deviation (ell A) (widths A) A.r A.c
            (profile A.small A.T A.d A.b x y free a)=
            actualDeviation A.small A.T A.b x y free A.r A.c (physical A.T A.d A.b a) from
            deviation_profile A.small A.T A.hTG A.d A.b x y free a A.r A.c hy hf,
          penalty_profile A S x y free a hy hf]
        simp only [nonroot_iff A S x y free _ (physical_supported A.T A.d A.b a)]
    _=_ := hsum

end ContingencyTables.RootedLiteralCount

end OAI
