import OAI.Combinatorics.ContingencyTables.Rooted.RootedComponentProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPenaltyProgram

namespace OAI

/-! # The executed component sums equal the root penalty

The root-only filter in the manuscript costs no separate test: every
nonroot has an empty root fibre.  This connects the polynomial grouped
signed-sum program to the actual selected-root discrepancy.
-/

namespace ContingencyTables.RootedComponentProgram

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

lemma componentTotal_zero (A : Instance I J) (S : Selection A.T)
    (d : I⊕J → ℤ) (a : I⊕J) (ha : a≠S.root a) :
    RootedRootPenalty.componentTotal A S d a=0 := by
  have hroot (v : I⊕J) : S.root v≠a := by
    intro hv
    apply ha
    calc
      a=S.root v := hv.symm
      _=S.root (S.root v) := (S.idempotent v).symm
      _=S.root a := congrArg S.root hv
  unfold RootedRootPenalty.componentTotal
  apply Finset.sum_eq_zero
  intro v _
  simp only [hroot v,ite_false,zero_mul]

theorem rootCount_eq_componentTotals (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) :
    RootedPenaltyProgram.rootCount A S x q=
      ∑ a,(RootedRootPenalty.componentTotal A S
        (ForestRootPenalty.smallDemand A.small A.X x q) a).natAbs := by
  unfold RootedPenaltyProgram.rootCount
  simp_rw [RootedRootPenalty.signedResidual_eq_small,Int.natAbs_neg]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a=S.root a
  · have hflag : RootedPenalty.rootFlag S a=true := decide_eq_true ha
    exact ite_eq_left hflag
  · rw [componentTotal_zero A S _ a ha]
    simp only [Int.natAbs_zero,ite_self]

/-- The positive and negative entries may be the actual row and column
small-view sums. Their difference is the only representation invariant
needed by the finite signed component program. -/
theorem total_records_rootCount (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) {n : ℕ} (e : Fin n ≃ I⊕J) (p m : Fin n → ℕ)
    (hd : ∀ i,(p i:ℤ)-m i=ForestRootPenalty.smallDemand A.small A.X x q (e i)) :
    total (records (fun i => e.symm (S.root (e i))) p m)=
      RootedPenaltyProgram.rootCount A S x q := by
  have hs (a : Fin n) :
      (∑ i,if e.symm (S.root (e i))=a then (p i:ℤ)-m i else 0)=
        RootedRootPenalty.componentTotal A S
          (ForestRootPenalty.smallDemand A.small A.X x q) (e a) := by
    calc
      _=∑ i,if S.root (e i)=e a then
          ForestRootPenalty.smallDemand A.small A.X x q (e i) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hd i]
        simp only [Equiv.symm_apply_eq]
      _=∑ v,if S.root v=e a then
          ForestRootPenalty.smallDemand A.small A.X x q v else 0 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _=_ := by
        simp only [RootedRootPenalty.componentTotal,ite_mul,one_mul,zero_mul]
  rw [total_records]
  calc
    _=∑ a,(RootedRootPenalty.componentTotal A S
        (ForestRootPenalty.smallDemand A.small A.X x q) (e a)).natAbs := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hs]
    _=∑ a,(RootedRootPenalty.componentTotal A S
        (ForestRootPenalty.smallDemand A.small A.X x q) a).natAbs :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _=_ := (rootCount_eq_componentTotals A S x q).symm

noncomputable def positiveDemand (A : Instance I J) (z : View A → ℕ) : I⊕J → ℕ :=
  Sum.elim
    (fun i => ∑ j,if A.small i j then (A.X i j).toNat else 0)
    (fun j => ∑ i,if A.small i j then A.b i j-ForestCountIdentification.smallY A.small z i j else 0)

noncomputable def negativeDemand (A : Instance I J) (z : View A → ℕ) : I⊕J → ℕ :=
  Sum.elim
    (fun i => ∑ j,if A.small i j then ForestCountIdentification.smallX A.small z i j else 0)
    (fun j => ∑ i,if A.small i j then (A.X i j).toNat else 0)

theorem naturalDemand_eq (A : Instance I J) (z : View A → ℕ) (a : I⊕J) :
    (positiveDemand A z a:ℤ)-negativeDemand A z a=
      ForestRootPenalty.smallDemand A.small A.X (ForestScaledPenalty.rowCounts A z)
        (ForestScaledPenalty.columnCounts A z) a := by
  cases a with
  | inl i =>
    simp only [positiveDemand,negativeDemand,Sum.elim_inl,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,
      ForestRootPenalty.smallDemand]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    cases A.small i j <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,sub_zero,
        ForestScaledPenalty.rowCounts,Int.toNat_of_nonneg (A.hX i j).1]
  | inr j =>
    simp only [positiveDemand,negativeDemand,Sum.elim_inr,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,
      ForestRootPenalty.smallDemand]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases A.small i j <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,sub_zero,
        ForestScaledPenalty.columnCounts,Int.toNat_of_nonneg (A.hX i j).1]

end ContingencyTables.RootedComponentProgram

end OAI
