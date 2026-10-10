import OAI.Combinatorics.ContingencyTables.Rooted.ForestAffineCoefficients

namespace OAI

/-! # The original integral forest solution is the cut-defined affine completion -/

namespace ContingencyTables.ForestAffineCoefficients

open scoped BigOperators Classical
open CompanionFactorialApplication GraphIntegralCompletion GraphCompletionCounts
open ForestCapacity ForestCut ForestPhysicalCompletion MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

lemma selected_nonroot (A : Instance I J) (t : TreeCell A.T) (v : I⊕J)
    (hv : cutSide A t v=true) : v≠componentRoot A.T v := by
  intro he
  let root := componentRoot A.T (.inl t.val.1)
  have hrootRoot : componentRoot A.T root=root := componentRoot_idempotent A.T (.inl t.val.1)
  have hreach : (A.T.deleteEdges {edge t.val}).Reachable (cutVertex A t) v := by
    simpa only [cutSide,side,decide_eq_true_eq] using hv
  have hcomp := (cut_properties A t).1.trans (hreach.mono (A.T.deleteEdges_le {edge t.val}))
  have hsame : componentRoot A.T v=root := by
    rw [← componentRoot_constant A.T hcomp,hrootRoot]
  have hvr : v=root := he.trans hsame
  have hbad : cutSide A t root=true := by simpa only [hvr] using hv
  exact Bool.false_ne_true ((cut_properties A t).2.1.symm.trans hbad)

lemma other_tree_sign_zero (A : Instance I J) (t : TreeCell A.T) (a : I×J)
    (ha : A.T.Adj (.inl a.1) (.inr a.2)) (hne : a≠t.val) : sign A t a=0 := by
  have hh := side_eq_of_tree_edge A.T (edge t.val) (cutVertex A t) ha
    (by intro he; exact hne (cell_edge_injective he))
  exact sub_eq_zero.mpr (congrArg indicator hh)

noncomputable def smallContribution (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℝ) : ℝ :=
  ∑ a : I×J,if A.small a.1 a.2 then
    indicator (cutSide A t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      indicator (cutSide A t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0

noncomputable def offset (A : Instance I J) (t : TreeCell A.T) (x q : I → J → ℝ) : ℝ :=
  A.X t.val.1 t.val.2-smallContribution A t x q/sign A t t.val-
    ∑ a : I×J,coefficient A t a*(A.X a.1 a.2:ℝ)

noncomputable def affineTree (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℝ) (z : I×J → ℝ) : ℝ :=
  AffinePenalty.affineValue (offset A t x q) (coefficient A t) z

/-- Isolating the actual selected tree edge in the root-away cut gives
its affine value for every real solution of the nonroot equations. -/
theorem affine_of_nonroot_equations (A : Instance I J) (t : TreeCell A.T)
    (x q z : I → J → ℝ)
    (hr : ∀ i,Sum.inl i≠componentRoot A.T (.inl i) →
      rowDifference A.small x z (fun i j => (A.X i j:ℝ)) i=0)
    (hc : ∀ j,Sum.inr j≠componentRoot A.T (.inr j) →
      columnDifference A.small q z (fun i j => (A.X i j:ℝ)) j=0) :
    z t.val.1 t.val.2=affineTree A t x q (fun a => z a.1 a.2) := by
  let f : I×J → ℝ := fun a => cutTerm A.small
    (fun i => cutSide A t (.inl i)) (fun j => cutSide A t (.inr j))
    x q z (fun i j => (A.X i j:ℝ)) a.1 a.2
  have hsum : (∑ a,f a)=0 := by
    rw [Fintype.sum_prod_type]
    exact cut_sum_zero A.small _ _ x q z _
      (fun i hi => hr i (selected_nonroot A t (.inl i) hi))
      (fun j hj => hc j (selected_nonroot A t (.inr j) hj))
  have hterm (a : I×J) : f a=
      (if a=t.val then sign A t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)+
      (if A.small a.1 a.2 then
        indicator (cutSide A t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          indicator (cutSide A t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0)-
      sign A t t.val*coefficient A t a*(z a.1 a.2-A.X a.1 a.2) := by
    by_cases he : a=t.val
    · subst a
      have hs : A.small t.val.1 t.val.2=false := A.hTG t.property
      simp only [f,cutTerm,hs,Bool.false_eq_true,ite_false,ite_true,coefficient,t.property,
        not_true_eq_false,and_false,sign,mul_zero,zero_mul,add_zero,sub_zero]
    · by_cases hs : A.small a.1 a.2=true
      · simp [f,cutTerm,hs,he,coefficient]
      · have hs' : A.small a.1 a.2=false := Bool.eq_false_iff.mpr hs
        by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
        · have hz := other_tree_sign_zero A t a ht he
          simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_true_eq_false,and_false,zero_add,mul_zero,zero_mul,sub_zero]
          change sign A t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=0
          rw [hz,zero_mul]
        · simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_false_eq_true,and_self,ite_true,zero_add,zero_sub]
          change sign A t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=
            -(sign A t t.val*(-sign A t a/sign A t t.val)*(z a.1 a.2-A.X a.1 a.2))
          field_simp [sign_self_ne_zero A t]
  simp_rw [hterm] at hsum
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  have hsingle : (∑ a : I×J,if a=t.val then sign A t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)=
      sign A t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2) := by simp
  rw [hsingle] at hsum
  change sign A t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2)+smallContribution A t x q-
    (∑ a : I×J,sign A t t.val*coefficient A t a*(z a.1 a.2-A.X a.1 a.2))=0 at hsum
  have hprod : (∑ a : I×J,sign A t t.val*coefficient A t a*(z a.1 a.2-A.X a.1 a.2))=
      sign A t t.val*((∑ a : I×J,coefficient A t a*z a.1 a.2)-
        ∑ a : I×J,coefficient A t a*(A.X a.1 a.2:ℝ)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hprod] at hsum
  unfold affineTree AffinePenalty.affineValue offset
  apply (mul_left_cancel₀ (sign_self_ne_zero A t))
  rw [mul_add,mul_sub,mul_sub,← mul_div_assoc,mul_div_cancel_left₀ _ (sign_self_ne_zero A t)]
  nlinarith [hsum]

/-- In particular this affine display is the original integral solution
used inside h_j, rather than an unrelated continuous extension. -/
theorem solved_eq_affine (A : Instance I J) (t : TreeCell A.T)
    (x q free : I → J → ℤ) :
    (solved A.small A.T A.r A.c x q free t.val.1 t.val.2:ℝ)=
      affineTree A t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
        (fun a => (free a.1 a.2:ℝ)) := by
  let z : I → J → ℝ := fun i j => (completed A.small A.T A.r A.c x q free i j:ℝ)
  have hh := affine_of_nonroot_equations A t (fun i j => (x i j:ℝ))
    (fun i j => (q i j:ℝ)) z (by
      intro i hi
      have hr := row_completed_sum A.small A.T A.hTG A.r A.c x q free i hi
      have hX := A.hXr i
      unfold rowDifference
      have he : (∑ j,if A.small i j then (x i j:ℝ) else z i j)=(A.r i:ℝ) := by
        dsimp only [z]
        exact_mod_cast hr
      have hX' : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast hX
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else z i j)-(∑ j,(A.X i j:ℝ)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> rfl
        _=0 := by rw [he,hX',sub_self]) (by
      intro j hj
      have hc := column_completed_sum A.small A.T A.hTG A.r A.c x q free j hj
      have hX := A.hXc j
      unfold columnDifference
      have he : (∑ i,if A.small i j then (q i j:ℝ) else z i j)=(A.c j:ℝ) := by
        dsimp only [z]
        exact_mod_cast hc
      have hX' : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast hX
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else z i j)-(∑ i,(A.X i j:ℝ)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _=0 := by rw [he,hX',sub_self])
  have hz : z t.val.1 t.val.2=(solved A.small A.T A.r A.c x q free t.val.1 t.val.2:ℝ) := by
    simp only [z,completed,t.property,ite_true]
  rw [hz] at hh
  rw [hh]
  unfold affineTree AffinePenalty.affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
  · simp only [coefficient,ht,not_true_eq_false,and_false,ite_false,zero_mul]
  · simp only [z,completed,ht,ite_false]

end ContingencyTables.ForestAffineCoefficients

end OAI
