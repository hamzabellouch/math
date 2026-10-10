import OAI.Combinatorics.ContingencyTables.Rooted.ForestPhysicalCompletion
import OAI.Combinatorics.ContingencyTables.Rooted.ForestLiteralCount

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestPhysicalCompletion ForestLiteralCount

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem completionFlow_divergence_all (G : SimpleGraph V) (r : V → ℤ) (a : V) :
    (∑ b, completionFlow G r a b)=
      r a-∑ v, if componentRoot G v=a then r v else 0 := by
  unfold completionFlow
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,walkFlow_sum,mul_sub,Finset.sum_sub_distrib]
  simp [mul_ite,eq_comm]

/-- Absolute component totals sum to at most the total absolute demand.
Each vertex is counted in one component, including isolated vertices. -/
theorem sum_abs_componentTotal (root : V → V) (r : V → ℝ) :
    (∑ a, |∑ v, if root v=a then r v else 0|)≤∑ v, |r v| := by
  calc
    _ ≤ ∑ a, ∑ v, |if root v=a then r v else 0| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      have he (a v : V) : |if root v=a then r v else 0|=
          if root v=a then |r v| else 0 := by split_ifs <;> simp
      simp_rw [he]
      rw [Finset.sum_comm]
      simp

end Generic

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Maximum capacity makes every original large edge stay within a tree
component, which is the exact cancellation needed at component roots. -/
lemma root_eq_large (small : I → J → Bool) (b : I → J → ℕ)
    (T : SimpleGraph (I⊕J)) (hT : T≤ForestCapacity.cellGraph small) (hacyc : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph (I⊕J), F≤ForestCapacity.cellGraph small → F.IsAcyclic →
      MaximumForest.weight F (ForestCapacity.capacity b)≤MaximumForest.weight T (ForestCapacity.capacity b))
    (hb : ∀ i j, small i j=false → 1≤b i j) (i : I) (j : J) (hs : small i j=false) :
    componentRoot T (.inl i)=componentRoot T (.inr j) := by
  have hcap : ∀ e∈(ForestCapacity.cellGraph small).edgeSet, 0<ForestCapacity.capacity b e := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    have hg : (ForestCapacity.cellGraph small).Adj u v := by simpa using he
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim hg
      | inr j => exact hb i j hg
    | inr j =>
      cases v with
      | inl i => exact hb i j hg
      | inr j' => exact False.elim hg
  have hspans := MaximumForest.maximum_spans (ForestCapacity.cellGraph small) T
    (ForestCapacity.capacity b) hT hacyc hmax hcap
  apply componentRoot_constant T
  rw [hspans]
  exact (show (ForestCapacity.cellGraph small).Adj (.inl i) (.inr j) from hs).reachable

lemma tableCompletion_row_all (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (r : I → ℤ) (c : J → ℤ) (i : I) :
    (∑ j, tableCompletion T r c i j)=
      r i-∑ v, if componentRoot T v=Sum.inl i then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := completionFlow_divergence_all T (Sum.elim r (fun j => -c j)) (.inl i)
  rw [Fintype.sum_sum_type] at hs
  have hzero : (∑ i', completionFlow T (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply completionFlow_supported
    intro h
    exact hT h
  simpa only [hzero,zero_add,Sum.elim_inl,tableCompletion] using hs

lemma tableCompletion_column_all (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (r : I → ℤ) (c : J → ℤ) (j : J) :
    -(∑ i, tableCompletion T r c i j)=
      -c j-∑ v, if componentRoot T v=Sum.inr j then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := completionFlow_divergence_all T (Sum.elim r (fun j => -c j)) (.inr j)
  rw [Fintype.sum_sum_type] at hs
  have hzero : (∑ j', completionFlow T (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply completionFlow_supported
    intro h
    exact hT h
  have hskew : (∑ i, completionFlow T (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i, tableCompletion T r c i j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact completionFlow_skew T _ _ _
  simpa only [hzero,add_zero,Sum.elim_inr,hskew] using hs

noncomputable def residualDemand (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) : I⊕J → ℤ :=
  Sum.elim (rowResidual small T r x free) (fun j => -columnResidual small T c q free j)

noncomputable def componentTotal (T : SimpleGraph (I⊕J)) (d : I⊕J → ℤ) (a : I⊕J) : ℤ :=
  ∑ v, (if componentRoot T v=a then 1 else 0)*d v

noncomputable def smallDemand (small : I → J → Bool) (X x q : I → J → ℤ) : I⊕J → ℤ :=
  Sum.elim (fun i => ∑ j, if small i j then X i j-x i j else 0)
    (fun j => ∑ i, if small i j then q i j-X i j else 0)

/-- Large-cell incidences cancel exactly within each component. The
component residual therefore depends only on the small views, not on
the chosen free values. -/
theorem componentTotal_residual (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free X : I → J → ℤ)
    (hr : ∀ i, (∑ j, X i j)=r i) (hc : ∀ j, (∑ i, X i j)=c j)
    (hroot : ∀ i j, small i j=false → componentRoot T (.inl i)=componentRoot T (.inr j))
    (a : I⊕J) :
    componentTotal T (residualDemand small T r c x q free) a=
      componentTotal T (smallDemand small X x q) a := by
  let R : I → ℤ := fun i => if componentRoot T (.inl i)=a then 1 else 0
  let C : J → ℤ := fun j => if componentRoot T (.inr j)=a then 1 else 0
  have hrow (i : I) : R i*rowResidual small T r x free i=
      ∑ j, R i*(X i j-fixedRow small T x free i j) := by
    rw [rowResidual,← hr i,← Finset.sum_sub_distrib,Finset.mul_sum]
  have hcol (j : J) : C j*(-columnResidual small T c q free j)=
      ∑ i, C j*(fixedColumn small T q free i j-X i j) := by
    rw [columnResidual,← hc j,neg_sub,← Finset.sum_sub_distrib,Finset.mul_sum]
  unfold componentTotal residualDemand smallDemand
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  change (∑ i, R i*rowResidual small T r x free i)+
      (∑ j, C j*(-columnResidual small T c q free j))=
    (∑ i, R i*(∑ j, if small i j then X i j-x i j else 0))+
      ∑ j, C j*(∑ i, if small i j then q i j-X i j else 0)
  simp_rw [hrow,hcol,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => C j*(fixedColumn small T q free i j-X i j)),
    Finset.sum_comm (f := fun j i => C j*(if small i j then q i j-X i j else 0)),
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : small i j=true
  · simp [fixedRow,fixedColumn,hs]
  · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
    have he : R i=C j := by unfold R C; rw [hroot i j hs']
    rw [he]
    simp only [fixedRow,fixedColumn,hs',Bool.false_eq_true,ite_false]
    ring

noncomputable def signedResidual (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) : I⊕J → ℤ :=
  Sum.elim
    (fun i => (∑ j, if small i j then x i j else completed small T r c x q free i j)-r i)
    (fun j => -((∑ i, if small i j then q i j else completed small T r c x q free i j)-c j))

/-- The actual completed table's signed root discrepancy is exactly the
negative component total of its original residual demands. -/
theorem signedResidual_eq_component (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (r : I → ℤ) (c : J → ℤ)
    (x q free : I → J → ℤ) (a : I⊕J) :
    signedResidual small T r c x q free a=
      -(∑ v, if componentRoot T v=a then residualDemand small T r c x q free v else 0) := by
  cases a with
  | inl i =>
    simp only [signedResidual,Sum.elim_inl]
    simp_rw [row_pointwise small T hT r c x q free]
    rw [Finset.sum_add_distrib]
    have hr := tableCompletion_row_all small T hT
      (rowResidual small T r x free) (columnResidual small T c q free) i
    change (∑ j, solved small T r c x q free i j)=_ at hr
    rw [hr]
    unfold residualDemand rowResidual columnResidual
    ring
  | inr j =>
    simp only [signedResidual,Sum.elim_inr]
    simp_rw [column_pointwise small T hT r c x q free]
    rw [Finset.sum_add_distrib]
    have hc := tableCompletion_column_all small T hT
      (rowResidual small T r x free) (columnResidual small T c q free) j
    change -(∑ i, solved small T r c x q free i j)=_ at hc
    have hc' : (∑ i, solved small T r c x q free i j)=
        columnResidual small T c q free j+
          ∑ v, if componentRoot T v=Sum.inr j then
            Sum.elim (rowResidual small T r x free) (fun j => -columnResidual small T c q free j) v else 0 := by
      linarith
    rw [hc']
    unfold residualDemand rowResidual columnResidual
    ring

theorem signedResidual_eq_small (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (r : I → ℤ) (c : J → ℤ)
    (x q free X : I → J → ℤ)
    (hr : ∀ i, (∑ j, X i j)=r i) (hc : ∀ j, (∑ i, X i j)=c j)
    (hroot : ∀ i j, small i j=false → componentRoot T (.inl i)=componentRoot T (.inr j))
    (a : I⊕J) : signedResidual small T r c x q free a=
      -componentTotal T (smallDemand small X x q) a := by
  rw [signedResidual_eq_component small T hT r c x q free a]
  have he : (∑ v, if componentRoot T v=a then residualDemand small T r c x q free v else 0)=
      componentTotal T (residualDemand small T r c x q free) a := by
    simp [componentTotal,ite_mul]
  rw [he,componentTotal_residual small T r c x q free X hr hc hroot a]

/-- The original root deviations do not depend on the free assignment;
this follows from the actual integral completion, rather than an assumed
affine representation of the source count. -/
theorem signedResidual_independent (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (r : I → ℤ) (c : J → ℤ)
    (x q free free' X : I → J → ℤ)
    (hr : ∀ i, (∑ j, X i j)=r i) (hc : ∀ j, (∑ i, X i j)=c j)
    (hroot : ∀ i j, small i j=false → componentRoot T (.inl i)=componentRoot T (.inr j)) :
    signedResidual small T r c x q free=signedResidual small T r c x q free' := by
  funext a
  rw [signedResidual_eq_small small T hT r c x q free X hr hc hroot a,
    signedResidual_eq_small small T hT r c x q free' X hr hc hroot a]

theorem sum_abs_signedResidual_le (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (b : I → J → ℕ)
    (r : I → ℤ) (c : J → ℤ) (x q free X : I → J → ℤ)
    (hr : ∀ i, (∑ j, X i j)=r i) (hc : ∀ j, (∑ i, X i j)=c j)
    (hroot : ∀ i j, small i j=false → componentRoot T (.inl i)=componentRoot T (.inr j))
    (hx : ∀ i j, small i j=true → 0≤x i j ∧ x i j≤b i j)
    (hq : ∀ i j, small i j=true → 0≤q i j ∧ q i j≤b i j)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j) :
    (∑ a, |(signedResidual small T r c x q free a:ℝ)|)≤
      2*∑ i, ∑ j, if small i j then (b i j:ℝ) else 0 := by
  have he (a : I⊕J) : (signedResidual small T r c x q free a:ℝ)=
      -(∑ v, if componentRoot T v=a then (smallDemand small X x q v:ℝ) else 0) := by
    rw [signedResidual_eq_small small T hT r c x q free X hr hc hroot a]
    unfold componentTotal
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : componentRoot T v=a <;> simp [hv]
  simp_rw [he,abs_neg]
  apply (sum_abs_componentTotal (componentRoot T) (fun v => (smallDemand small X x q v:ℝ))).trans
  have hrow (i : I) :
      |((∑ j, if small i j then X i j-x i j else 0:ℤ):ℝ)|≤
        ∑ j, if small i j then (b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hs : small i j=true
    · simp only [hs,ite_true]
      have hh : |X i j-x i j|≤(b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(hx i j hs).1,(hx i j hs).2,(hX i j).1,(hX i j).2]
      exact_mod_cast hh
    · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hcol (j : J) :
      |((∑ i, if small i j then q i j-X i j else 0:ℤ):ℝ)|≤
        ∑ i, if small i j then (b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hs : small i j=true
    · simp only [hs,ite_true]
      have hh : |q i j-X i j|≤(b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(hq i j hs).1,(hq i j hs).2,(hX i j).1,(hX i j).2]
      exact_mod_cast hh
    · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  rw [Fintype.sum_sum_type]
  change (∑ i, |((∑ j, if small i j then X i j-x i j else 0:ℤ):ℝ)|)+
      (∑ j, |((∑ i, if small i j then q i j-X i j else 0:ℤ):ℝ)|)≤_
  have hrows := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  have hcols := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcol j)
  rw [Finset.sum_comm] at hcols
  linarith

lemma abs_actualDeviation_solved (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b x y free : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (a : I⊕J) :
    |actualDeviation small T b x y free r c
      (solved small T r c (fun i j => (x i j:ℤ))
        (fun i j => ((b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ))) a|=
      |(signedResidual small T r c (fun i j => (x i j:ℤ))
        (fun i j => ((b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ)) a:ℝ)| := by
  cases a with
  | inl i =>
    simp only [actualDeviation,signedResidual,Sum.elim_inl,completed,largeValue]
    push_cast
    rfl
  | inr j =>
    simp only [actualDeviation,signedResidual,Sum.elim_inr,completed,largeValue]
    push_cast
    rw [abs_neg]

/-- This is the root part of the source's actual penalty. Each small
cell contributes at most its capacity at each of its two incidences. -/
theorem rootPenalty_le (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (b x y free : I → J → ℕ)
    (r : I → ℤ) (c : J → ℤ) (X : I → J → ℤ)
    (hr : ∀ i, (∑ j, X i j)=r i) (hc : ∀ j, (∑ i, X i j)=c j)
    (hroot : ∀ i j, small i j=false → componentRoot T (.inl i)=componentRoot T (.inr j))
    (hx : ∀ i j, small i j=true → x i j≤b i j)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j) :
    (∑ a, if ForestPenaltyApplication.rootFlag T a then
      |actualDeviation small T b x y free r c
        (solved small T r c (fun i j => (x i j:ℤ))
          (fun i j => ((b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ))) a| else 0)≤
      2*∑ i, ∑ j, if small i j then (b i j:ℝ) else 0 := by
  apply le_trans (Finset.sum_le_sum (fun a _ => ?_))
    (sum_abs_signedResidual_le small T hT b r c
      (fun i j => (x i j:ℤ)) (fun i j => ((b i j-y i j:ℕ):ℤ))
      (fun i j => (free i j:ℤ)) X hr hc hroot
      (by intro i j hs; exact ⟨by positivity,by exact_mod_cast hx i j hs⟩)
      (by intro i j _; exact ⟨by positivity,by exact_mod_cast Nat.sub_le (b i j) (y i j)⟩)
      hX)
  split_ifs
  · exact (abs_actualDeviation_solved small T b x y free r c a).le
  · exact abs_nonneg _

end ContingencyTables.ForestRootPenalty

end OAI
