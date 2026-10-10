import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPhysicalMarginal
import OAI.Combinatorics.ContingencyTables.Sampling.RepairFibres

namespace OAI

/-! # Completion-retaining fibres of the literal hard marginal

Each physical large-cell assignment with zero penalty is exactly one pair
of full row and column views. The retained small profile is prescribed,
while large entries agree. No completion multiplicity is discarded.
-/

namespace ContingencyTables.PhysicalCompletionFibres

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles RowColumnPenalties
open FirstPaperPhysicalMarginal PaddedCompletions NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev SmallProfile (small : I → J → Bool) :=
  SmallView (fun a : I×J => small a.1 a.2) → ℕ

/-- Full row/column views with one prescribed small profile. -/
def CompletionFibre (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) :=
  {Z : RowColumnPair rbar cbar //
    (∀ i, smallRow small Z.val.1 i ≤ r i) ∧
    (∀ j, smallColumnView small Z.val.2 j ≤ c j) ∧
    (∀ i j (hs : small i j=true),
      Z.val.1 i j=z (⟨(i,j),hs⟩,false) ∧
      Z.val.2 i j=B i j-z (⟨(i,j),hs⟩,true)) ∧
    (∀ i j, small i j=false → Z.val.1 i j=Z.val.2 i j) ∧
    (∀ i j, small i j=false → Z.val.1 i j ≤ B i j)}

noncomputable instance completionFibreFintype (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) :
    Fintype (CompletionFibre small B r rbar c cbar z) := by
  unfold CompletionFibre
  infer_instance

omit [Fintype I] [Fintype J] in
lemma physical_inBox (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : ∀ u, z u ≤ B u.1.val.1 u.1.val.2)
    (a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)) :
    BalancedBox.InBox (fun u => B u.1.1 u.1.2)
      (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a) := by
  rintro ⟨⟨i,j⟩,b⟩
  by_cases hs : small i j=true
  · simpa only [physicalProfile,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,b)
  · cases b
    · simpa only [physicalProfile,hs,dite_eq_right,Bool.false_eq_true,↓reduceIte,↓reduceDIte] using
        Nat.le_of_lt_succ (a ⟨(i,j),Bool.eq_false_iff.mpr hs⟩).isLt
    · simp only [physicalProfile,hs,↓reduceIte]
      exact Nat.sub_le _ _

noncomputable def fibreAssignment {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small}
    (Z : CompletionFibre small B r rbar c cbar z) :
    PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) :=
  fun a => ⟨Z.val.val.1 a.val.1 a.val.2,
    Nat.lt_succ_of_le (Z.property.2.2.2.2 _ _ a.property)⟩

lemma fibreAssignment_views {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small}
    (Z : CompletionFibre small B r rbar c cbar z) :
    let p := physicalProfile (fun a : I×J => small a.1 a.2)
      (fun a => B a.1 a.2) z (fibreAssignment Z)
    rowView p=Z.val.val.1 ∧ columnView B p=Z.val.val.2 := by
  dsimp only
  constructor
  · funext i j
    by_cases hs : small i j=true
    · simpa only [rowView,physicalProfile,hs,dite_eq_left] using
        (Z.property.2.2.1 i j hs).1.symm
    · simp only [rowView,physicalProfile,hs,Bool.false_eq_true,↓reduceIte,↓reduceDIte]
      rfl
  · funext i j
    by_cases hs : small i j=true
    · simpa only [columnView,physicalProfile,hs,dite_eq_left] using
        (Z.property.2.2.1 i j hs).2.symm
    · simp only [columnView,physicalProfile,hs,Bool.false_eq_true,↓reduceIte,↓reduceDIte,fibreAssignment]
      rw [Nat.sub_sub_self (Z.property.2.2.2.2 i j (Bool.eq_false_iff.mpr hs))]
      exact Z.property.2.2.2.1 i j (Bool.eq_false_iff.mpr hs)

noncomputable def zeroPhysicalEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u, z u ≤ B u.1.val.1 u.1.val.2) :
    {a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) //
      penalty cellLine (smallCoordinate small)
        (fullOffset B (fun i => r i+rowLargeCount small i*L)
          (fun j => c j+columnLargeCount small j*L)) viewSlope
        (smallOffset small B r c) viewSlope
        (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a)=0} ≃
      CompletionFibre small B (r) (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) z where
  toFun a := by
    let p := physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a.val
    have hp := (penalty_zero_iff small B r _ c _ p (physical_inBox small B z hz a.val)).mp a.property
    refine ⟨⟨(rowView p,columnView B p),hp.1,hp.2.1⟩,hp.2.2.1,hp.2.2.2,?_,?_,?_⟩
    · intro i j hs
      simp [p,rowView,columnView,physicalProfile,hs]
    · intro i j hs
      have hcap := Nat.le_of_lt_succ (a.val ⟨(i,j),hs⟩).isLt
      simpa only [p,rowView,columnView,physicalProfile,hs,Bool.false_eq_true,dite_eq_right,
        ↓reduceIte,↓reduceDIte,Prod.fst,Prod.snd] using (Nat.sub_sub_self hcap).symm
    · intro i j hs
      simpa only [p,rowView,physicalProfile,hs,Bool.false_eq_true,dite_eq_right,
        ↓reduceIte,↓reduceDIte,Prod.fst] using Nat.le_of_lt_succ (a.val ⟨(i,j),hs⟩).isLt
  invFun Z := by
    refine ⟨fibreAssignment Z,?_⟩
    have hp := fibreAssignment_views Z
    apply (penalty_zero_iff small B r _ c _ _ (physical_inBox small B z hz _)).mpr
    unfold FullConditions
    rw [hp.1,hp.2]
    exact ⟨Z.val.property.1,Z.val.property.2,Z.property.1,Z.property.2.1⟩
  left_inv a := by
    apply Subtype.ext
    funext l
    apply Fin.ext
    simp only [fibreAssignment,rowView,physicalProfile,l.property,Bool.false_eq_true,
      ↓reduceIte,↓reduceDIte]
  right_inv Z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (fibreAssignment_views Z).1 (fibreAssignment_views Z).2

/-- Exact equality, including all completion multiplicities. -/
theorem hardMarginal_eq_fibre_card (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u, z u ≤ B u.1.val.1 u.1.val.2) :
    hardMarginal small B r c L z=
      (Fintype.card (CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) z):ℝ) := by
  unfold hardMarginal fullHardFamily hardWeight
  rw [Finset.sum_boole,←Fintype.card_subtype]
  exact_mod_cast Fintype.card_congr (zeroPhysicalEquiv small B r c L z hz)

/-- Forgetting the retained profile loses no information on a bounded
injective family of profiles. In particular all later fibre sums count
full state/completion pairs exactly once. -/
theorem fibre_projection_injective {S : Type*}
    (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (p : S → SmallProfile small)
    (hp : Function.Injective p) (hbox : ∀ s u, p s u ≤ B u.1.val.1 u.1.val.2) :
    Function.Injective (fun a : (s : S) × CompletionFibre small B r rbar c cbar (p s) =>
      a.2.val) := by
  rintro ⟨s,X⟩ ⟨t,Y⟩ he
  have hst : s=t := by
    apply hp
    funext u
    rcases u with ⟨⟨⟨i,j⟩,hs⟩,b⟩
    cases b
    · have hx := congrArg (fun Z : RowColumnPair rbar cbar => Z.val.1 i j) he
      rw [(X.property.2.2.1 i j hs).1,(Y.property.2.2.1 i j hs).1] at hx
      exact hx
    · have hq := congrArg (fun Z : RowColumnPair rbar cbar => Z.val.2 i j) he
      rw [(X.property.2.2.1 i j hs).2,(Y.property.2.2.1 i j hs).2] at hq
      have hx := hbox s (⟨(i,j),hs⟩,true)
      have hy := hbox t (⟨(i,j),hs⟩,true)
      dsimp only at hx hy
      omega
  subst t
  congr 1
  exact Subtype.ext he

end ContingencyTables.PhysicalCompletionFibres

end OAI
