import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextFibres

namespace OAI

/-! # Literal contextual mass domination by repair

Finite sums of the actual hard completion weights, including all large
completions, are compared by the concrete repair injection.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [LinearOrder I] [LinearOrder J]

abbrev BalancedPairs (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (s : I×J) (σ : I×J → ℕ) (k : ℕ) :=
  (z : BalancedProfiles small B s σ k) ×
    CompletionFibre small B r rbar c cbar (naturalProfile z.val)

noncomputable def balancedPairChild {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s : I×J} {σ : I×J → ℕ} {k : ℕ}
    (hs : small s.1 s.2=true)
    (a : BalancedPairs small B r rbar c cbar s σ k) :
    SmallResidualChild small r rbar c cbar s σ k := by
  have hq := balanced_fibre_views a.2 a.1.property.1
  refine ⟨⟨⟨a.2.val.val.1,a.2.val.property.1,?_⟩,a.2.property.1,?_⟩,?_,?_⟩
  · simpa only [hq] using a.2.val.property.2
  · simpa only [hq] using a.2.property.2.1
  · intro i j hs hbefore
    change a.2.val.val.1 i j=σ (i,j)
    rw [(a.2.property.2.2.1 i j hs).1]
    simpa only [smallView,hs,dite_eq_left] using a.1.property.2.1 i j hs hbefore
  · change a.2.val.val.1 s.1 s.2=k
    rw [(a.2.property.2.2.1 s.1 s.2 hs).1]
    simpa only [smallView,hs,dite_eq_left] using a.1.property.2.2

omit [DecidableEq I] [DecidableEq J] in
lemma balancedPairChild_injective {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s : I×J} {σ : I×J → ℕ} {k : ℕ}
    (hs : small s.1 s.2=true) :
    Function.Injective (balancedPairChild (B := B) (r := r) (rbar := rbar)
      (c := c) (cbar := cbar) (σ := σ) (k := k) hs) := by
  intro a b he
  apply fibre_projection_injective small B r rbar c cbar
    (fun z : BalancedProfiles small B s σ k => naturalProfile z.val)
    (fun x y h => Subtype.ext (naturalProfile_injective small B h))
    (fun z => naturalProfile_bounded z.val)
  apply Subtype.ext
  have hx := congrArg (fun T : SmallResidualChild small r rbar c cbar s σ k => T.val.val.val) he
  apply Prod.ext hx
  rw [←balanced_fibre_views a.2 a.1.property.1,←balanced_fibre_views b.2 b.1.property.1]
  exact hx

omit [DecidableEq I] [DecidableEq J] in
/-- Every residual table has exactly one balanced retained profile and
one large completion, provided the declared capacities exclude none. -/
lemma balancedPairChild_surjective {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s : I×J} {σ : I×J → ℕ} {k : ℕ}
    (hs : small s.1 s.2=true)
    (hcap : ∀ T : ResidualTables small r c rbar cbar, ∀ i j, T.val.val i j ≤ B i j) :
    Function.Surjective (balancedPairChild (B := B) (r := r) (rbar := rbar)
      (c := c) (cbar := cbar) (σ := σ) (k := k) hs) := by
  intro T
  let z : BoundedProfile small B := fun u =>
    if u.2 then ⟨B u.1.val.1 u.1.val.2-T.val.val.val u.1.val.1 u.1.val.2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    else ⟨T.val.val.val u.1.val.1 u.1.val.2,
      Nat.lt_succ_of_le (hcap T.val _ _)⟩
  have hzfalse (i : I) (j : J) (hij : small i j=true) :
      smallView small (naturalProfile z) false i j=T.val.val.val i j := by
    simp only [smallView,hij,dite_eq_left,naturalProfile,z,Bool.false_eq_true,↓reduceIte]
  have hztrue (i : I) (j : J) (hij : small i j=true) :
      smallQ small B (naturalProfile z) i j=T.val.val.val i j := by
    simp only [smallQ,hij,dite_eq_left,naturalProfile,z,↓reduceIte]
    exact Nat.sub_sub_self (hcap T.val i j)
  have hbal : ∀ i j, smallView small (naturalProfile z) false i j=
      smallQ small B (naturalProfile z) i j := by
    intro i j
    cases hij : small i j
    · simp only [smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte]
    · rw [hzfalse i j hij,hztrue i j hij]
  let w : BalancedProfiles small B s σ k := ⟨z,hbal,
    (fun i j hij hbefore => by rw [hzfalse i j hij]; exact T.property.1 i j hij hbefore),
    by rw [hzfalse s.1 s.2 hs]; exact T.property.2⟩
  let Z : CompletionFibre small B r rbar c cbar (naturalProfile w.val) :=
    ⟨⟨(T.val.val.val,T.val.val.val),T.val.val.property⟩,T.val.property.1,T.val.property.2,
      (fun i j hij => ⟨by
        change T.val.val.val i j=naturalProfile z (⟨(i,j),hij⟩,false)
        simpa only [smallView,hij,dite_eq_left] using (hzfalse i j hij).symm,by
        change T.val.val.val i j=B i j-naturalProfile z (⟨(i,j),hij⟩,true)
        simpa only [smallQ,hij,dite_eq_left] using (hztrue i j hij).symm⟩),
      (fun _ _ _ => rfl),(fun i j _ => hcap T.val i j)⟩
  refine ⟨⟨w,Z⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- A contextual child mass is the exact cardinality of full residual
tables in that child, including all large completion multiplicities. -/
theorem balanced_mass_eq_child_card (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (σ : I×J → ℕ) (k : ℕ)
    (hs : small s.1 s.2=true)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    (∑ z : BalancedProfiles small B s σ k,
      hardMarginal small B r c L (naturalProfile z.val))=
      (Fintype.card (SmallResidualChild small r (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) s σ k):ℝ) := by
  rw [sum_hard_eq_sigma_card small B r c L
    (fun z : BalancedProfiles small B s σ k => naturalProfile z.val)
    (fun z => naturalProfile_bounded z.val)]
  exact_mod_cast Fintype.card_congr (Equiv.ofBijective (balancedPairChild hs)
    ⟨balancedPairChild_injective hs,balancedPairChild_surjective hs hcap⟩)

noncomputable def defectPairContext {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (a : (z : DefectProfiles small B s t σ l) ×
      CompletionFibre small B r rbar c cbar (naturalProfile z.val)) :
    SmallJointDefectContext small r rbar c cbar s t σ l := by
  refine ⟨⟨a.2.val,defect_fibre_views a.2 hs ht a.1.property.1,
    a.2.property.1,a.2.property.2.1⟩,?_,?_⟩
  · intro i j hij hbefore
    rw [(a.2.property.2.2.1 i j hij).1]
    simpa only [smallView,hij,dite_eq_left] using a.1.property.2.1 i j hij hbefore
  · rw [(a.2.property.2.2.1 s.1 s.2 hs).1]
    simpa only [smallView,hs,dite_eq_left] using a.1.property.2.2

lemma defectPairContext_injective {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) :
    Function.Injective (defectPairContext (B := B) (r := r) (rbar := rbar)
      (c := c) (cbar := cbar) (σ := σ) (l := l) hs ht) := by
  intro a b he
  apply fibre_projection_injective small B r rbar c cbar
    (fun z : DefectProfiles small B s t σ l => naturalProfile z.val)
    (fun x y h => Subtype.ext (naturalProfile_injective small B h))
    (fun z => naturalProfile_bounded z.val)
  exact congrArg (fun Z : SmallJointDefectContext small r rbar c cbar s t σ l => Z.val.val) he

/-- Conditional repair domination for the actual weighted finite sums. -/
theorem conditional_defect_mass_le
    (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ)
    (L : ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    (∑ z : DefectProfiles small B s t σ l,
      hardMarginal small B r c L (naturalProfile z.val)) ≤
      ∑ z : BalancedProfiles small B s σ (l-1+if t.1=s.1 then 1 else 0),
        hardMarginal small B r c L (naturalProfile z.val) := by
  rw [sum_hard_eq_sigma_card small B r c L
    (fun z : DefectProfiles small B s t σ l => naturalProfile z.val)
    (fun z => naturalProfile_bounded z.val),
    balanced_mass_eq_child_card small B r c L s σ _ hs hcap]
  exact_mod_cast (Fintype.card_le_of_injective (defectPairContext hs ht)
    (defectPairContext_injective hs ht)).trans
    (smallContext_card_le small r _ c _ s t σ l hs ht hst)

omit [DecidableEq I] [DecidableEq J] [LinearOrder I] [LinearOrder J] in
/-- The manuscript's actual capacity excludes no residual table. -/
theorem paper_residual_capacity (r : I → ℕ) (c : J → ℕ) (d L U : ℕ)
    (hd : Fintype.card I*Fintype.card J ≤ d)
    (T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)) (i : I) (j : J) :
    T.val.val i j ≤ paperCapacity (firstPaperSmall r c U) r d L U i j := by
  let small := firstPaperSmall r c U
  change T.val.val i j ≤ paperCapacity small r d L U i j
  cases hs : small i j
  · have he := entry_le_total T.val.property i j
    have hcount := (large_count_le_dimension small).trans hd
    have heq : (∑ k, (r k+rowLargeCount small k*L))=
        (∑ k, r k)+(∑ k, rowLargeCount small k)*L := by
      rw [Finset.sum_add_distrib,Finset.sum_mul]
    rw [heq] at he
    have hb := Nat.mul_le_mul_right L hcount
    simp only [paperCapacity,hs,Bool.false_eq_true,↓reduceIte]
    omega
  · have hr := (entry_le_smallRow small T.val.val i j hs).trans (T.property.1 i)
    have hc := (entry_le_smallColumn small T.val.val i j hs).trans (T.property.2 j)
    have hinc : r i<U ∨ c j<U := by simpa only [small,firstPaperSmall,decide_eq_true_eq] using hs
    simp only [paperCapacity,hs,↓reduceIte]
    rcases hinc with hinc|hinc <;> omega

/-- The literal first-paper contextual repair bound has no capacity
hypothesis: its formal C excludes no full padded completion. -/
theorem firstPaper_conditional_defect_mass_le (r : I → ℕ) (c : J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ)
    (hs : paperSmall r c s.1 s.2=true) (ht : paperSmall r c t.1 t.2=true)
    (hst : RowMajorBefore s t) :
    let d := dimensionAllowance (I := I) (J := J)
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) (d^20)
    (∑ z : DefectProfiles small B s t σ l,
      hardMarginal small B r c (d^12) (naturalProfile z.val)) ≤
      ∑ z : BalancedProfiles small B s σ (l-1+if t.1=s.1 then 1 else 0),
        hardMarginal small B r c (d^12) (naturalProfile z.val) := by
  dsimp only
  apply conditional_defect_mass_le _ _ r c _ s t σ l hs ht hst
  exact paper_residual_capacity r c _ _ _ dimension_le_allowance

end ContingencyTables.SmallContextFibres

end OAI
