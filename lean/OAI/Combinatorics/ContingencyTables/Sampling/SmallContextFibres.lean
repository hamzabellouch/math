import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalCompletionFibres

namespace OAI

/-! # Actual small-prefix fibres and conditional repair

Only small cells in the row-major prefix are fixed. Large completions
remain free and retain their full counting multiplicity.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal LargePairEnumeration

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

abbrev BoundedProfile (small : I → J → Bool) (B : I → J → ℕ) :=
  (u : SmallView (fun a : I×J => small a.1 a.2)) → Fin (B u.1.val.1 u.1.val.2+1)

def naturalProfile {small : I → J → Bool} {B : I → J → ℕ}
    (z : BoundedProfile small B) : SmallProfile small := fun u => (z u).val

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma naturalProfile_injective (small : I → J → Bool) (B : I → J → ℕ) :
    Function.Injective (naturalProfile (small := small) (B := B)) := by
  intro x y he
  funext u
  exact Fin.ext (congrFun he u)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma naturalProfile_bounded {small : I → J → Bool} {B : I → J → ℕ}
    (z : BoundedProfile small B) (u) : naturalProfile z u ≤ B u.1.val.1 u.1.val.2 :=
  Nat.le_of_lt_succ (z u).isLt

noncomputable def smallQ (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then B i j-z (⟨(i,j),hs⟩,true) else 0

def SmallPrefix [LT I] [LT J] (small : I → J → Bool) (s : I×J)
    (σ : I×J → ℕ) (X : I → J → ℕ) : Prop :=
  ∀ i j, small i j=true → RowMajorBefore (i,j) s → X i j=σ (i,j)

def BalancedProfiles [LT I] [LT J] (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ) :=
  {z : BoundedProfile small B //
    (∀ i j, smallView small (naturalProfile z) false i j=smallQ small B (naturalProfile z) i j) ∧
    SmallPrefix small s σ (smallView small (naturalProfile z) false) ∧
    smallView small (naturalProfile z) false s.1 s.2=k}

def DefectProfiles [LT I] [LT J] (small : I → J → Bool) (B : I → J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :=
  {z : BoundedProfile small B //
    IsDefect (smallView small (naturalProfile z) false) (smallQ small B (naturalProfile z)) s t ∧
    SmallPrefix small s σ (smallView small (naturalProfile z) false) ∧
    smallView small (naturalProfile z) false s.1 s.2=l-1}

def SmallResidualChild [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ) :=
  {T : ResidualTables small r c rbar cbar //
    SmallPrefix small s σ T.val.val ∧ T.val.val s.1 s.2=k}

def SmallJointDefectContext [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :=
  {Z : JointDefect small r c rbar cbar s t //
    SmallPrefix small s σ Z.val.val.1 ∧ Z.val.val.1 s.1 s.2=l-1}

noncomputable instance balancedProfilesFintype [LT I] [LT J]
    (small : I → J → Bool) (B : I → J → ℕ) (s : I×J) (σ : I×J → ℕ) (k : ℕ) :
    Fintype (BalancedProfiles small B s σ k) := by unfold BalancedProfiles; infer_instance

noncomputable instance defectProfilesFintype [LT I] [LT J]
    (small : I → J → Bool) (B : I → J → ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :
    Fintype (DefectProfiles small B s t σ l) := by unfold DefectProfiles; infer_instance

noncomputable instance smallResidualChildFintype [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ) :
    Fintype (SmallResidualChild small r rbar c cbar s σ k) := by
  unfold SmallResidualChild
  infer_instance

noncomputable instance smallJointDefectContextFintype [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :
    Fintype (SmallJointDefectContext small r rbar c cbar s t σ l) := by
  unfold SmallJointDefectContext
  infer_instance

/-- The contextual injection fixes only earlier small entries. -/
theorem smallContext_card_le [LinearOrder I] [LinearOrder J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t) :
    Fintype.card (SmallJointDefectContext small r rbar c cbar s t σ l) ≤
      Fintype.card (SmallResidualChild small r rbar c cbar s σ
        (l-1+if t.1=s.1 then 1 else 0)) := by
  let f : SmallJointDefectContext small r rbar c cbar s t σ l →
      SmallResidualChild small r rbar c cbar s σ (l-1+if t.1=s.1 then 1 else 0) :=
    fun Z => ⟨jointRepair hs ht Z.val,(fun i j hij hbefore => by
      change repairMatrix Z.val.val.val.1 s t i j=σ (i,j)
      rw [repairMatrix_prefix Z.val.property.1 hst hbefore]
      exact Z.property.1 i j hij hbefore),by
      change repairMatrix Z.val.val.val.1 s t s.1 s.2=_
      rw [repairMatrix_special Z.val.property.1,Z.property.2]⟩
  apply Fintype.card_le_of_injective f
  intro X Y he
  apply Subtype.ext
  apply jointRepair_injective hs ht
  exact congrArg Subtype.val he

omit [DecidableEq I] [DecidableEq J] in
/-- A balanced small profile is balanced as a full pair of views. -/
lemma balanced_fibre_views {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small}
    (Z : CompletionFibre small B r rbar c cbar z)
    (hb : ∀ i j, smallView small z false i j=smallQ small B z i j) :
    Z.val.val.1=Z.val.val.2 := by
  funext i j
  cases hs : small i j
  · exact Z.property.2.2.2.1 i j hs
  · obtain ⟨hx,hq⟩ := Z.property.2.2.1 i j hs
    rw [hx,hq]
    simpa only [smallView,smallQ,hs,dite_eq_left] using hb i j

/-- The defect equation extends over the unchanged large completion. -/
lemma defect_fibre_views {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small} {s t : I×J}
    (Z : CompletionFibre small B r rbar c cbar z)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t) :
    IsDefect Z.val.val.1 Z.val.val.2 s t := by
  refine ⟨hd.1,?_⟩
  intro i j
  cases hij : small i j
  · have hns : ¬(i=s.1 ∧ j=s.2) := by rintro ⟨rfl,rfl⟩; rw [hs] at hij; contradiction
    have hnt : ¬(i=t.1 ∧ j=t.2) := by rintro ⟨rfl,rfl⟩; rw [ht] at hij; contradiction
    rw [←Z.property.2.2.2.1 i j hij]
    simp only [transferInt,hns,hnt,↓reduceIte,sub_zero,add_zero]
  · obtain ⟨hx,hq⟩ := Z.property.2.2.1 i j hij
    have he := hd.2 i j
    simp only [smallView,smallQ,hij,dite_eq_left,transferInt] at he
    simpa only [transferInt,hx,hq] using he

omit [DecidableEq I] [DecidableEq J] in
/-- Summing the literal hard weights is exactly counting the dependent
union of completion fibres. -/
theorem sum_hard_eq_sigma_card {S : Type*} [Fintype S]
    (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ)
    (L : ℕ) (p : S → SmallProfile small)
    (hbox : ∀ s u, p s u ≤ B u.1.val.1 u.1.val.2) :
    (∑ s, hardMarginal small B r c L (p s))=
      (Fintype.card ((s : S) × CompletionFibre small B r
        (fun i => r i+rowLargeCount small i*L) c
        (fun j => c j+columnLargeCount small j*L) (p s)):ℝ) := by
  simp_rw [hardMarginal_eq_fibre_card small B r c L _ (hbox _)]
  rw [Fintype.card_sigma]
  simp only [Nat.cast_sum]

end ContingencyTables.SmallContextFibres

end OAI
