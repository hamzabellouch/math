import OAI.Combinatorics.ContingencyTables.Sampling.SmallGraphProfiles

namespace OAI

/-! # Integer tests for balanced and single-defect small profiles -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small)

omit [LinearOrder I] [LinearOrder J] in
private lemma cell_eq_coordinates (a b : Cells small) :
    a=b ↔ a.val.1=b.val.1 ∧ a.val.2=b.val.2 := by
  simp only [Subtype.ext_iff,Prod.ext_iff]

omit [LinearOrder I] [LinearOrder J] in
private lemma view_at_cell (a : Cells small) (b : Bool) :
    smallView small z b a.val.1 a.val.2=z (a,b) := by
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
  simp only [smallView,a.property,dite_true,heta]

omit [LinearOrder I] [LinearOrder J] in
private lemma q_at_cell (a : Cells small) :
    smallQ small B z a.val.1 a.val.2=B a.val.1 a.val.2-z (a,true) := by
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
  simp only [smallQ,a.property,dite_true,heta]

def CellSumBalanced : Prop :=
  ∀ a : Cells small,z (a,false)+z (a,true)=B a.val.1 a.val.2

def CellSumDefect (s t : Cells small) : Prop :=
  s≠t ∧ ∀ a : Cells small,
    z (a,false)+z (a,true)+(if a=s then 1 else 0)=
      B a.val.1 a.val.2+(if a=t then 1 else 0)

omit [LinearOrder I] [LinearOrder J] in
theorem balanced_iff_cellSums
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) :
    Balanced small B z ↔ CellSumBalanced small B z := by
  constructor
  · intro h a
    have ha := h a.val.1 a.val.2
    rw [view_at_cell,q_at_cell] at ha
    have hba := hb a
    omega
  · intro h i j
    by_cases hs : small i j=true
    · let a : Cells small := ⟨(i,j),hs⟩
      have ha : z (a,false)+z (a,true)=B i j := h a
      simp only [smallView,smallQ,hs,dite_true]
      change z (a,false)=B i j-z (a,true)
      omega
    · simp [smallView,smallQ,hs]

/-- On bounded coordinates the signed defect equation is precisely an
equality of nonnegative integer sums. This avoids truncated subtraction
in the executable profile-pattern test. -/
theorem defect_iff_cellSums
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2)
    (s t : Cells small) :
    IsDefect (smallView small z false) (smallQ small B z) s.val t.val ↔
      CellSumDefect small B z s t := by
  constructor
  · intro h
    refine ⟨fun he => h.1 (congrArg Subtype.val he),?_⟩
    intro a
    have ha := h.2 a.val.1 a.val.2
    have hba := hb a
    simp only [transferInt,view_at_cell,q_at_cell,←cell_eq_coordinates] at ha
    split_ifs at ha ⊢ <;> omega
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (Subtype.ext he),?_⟩
    intro i j
    by_cases hs : small i j=true
    · let a : Cells small := ⟨(i,j),hs⟩
      have ha := h a
      have hba := hb a
      simp only [cell_eq_coordinates] at ha
      dsimp only [a] at ha hba
      simp only [smallQ,smallView,transferInt,hs,dite_true]
      split_ifs at ha ⊢ <;> omega
    · have hns : ¬(i=s.val.1 ∧ j=s.val.2) := by
        rintro ⟨rfl,rfl⟩
        exact hs s.property
      have hnt : ¬(i=t.val.1 ∧ j=t.val.2) := by
        rintro ⟨rfl,rfl⟩
        exact hs t.property
      simp only [smallQ,smallView,transferInt,hs,hns,hnt,ite_false]
      norm_num

/-- An allowed profile is detected by one balanced test or by one of
the ordered cell-pair tests. This uses at most quadratically many labels. -/
theorem pattern_iff_cellSums
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) :
    Pattern small B z ↔ CellSumBalanced small B z ∨
      ∃ s t : Cells small,CellSumDefect small B z s t := by
  constructor
  · rintro (h|⟨s,t,hs,ht,hd⟩)
    · exact Or.inl ((balanced_iff_cellSums small B z hb).mp h)
    · exact Or.inr ⟨⟨s,hs⟩,⟨t,ht⟩,(defect_iff_cellSums small B z hb _ _).mp hd⟩
  · rintro (h|⟨s,t,h⟩)
    · exact Or.inl ((balanced_iff_cellSums small B z hb).mpr h)
    · exact Or.inr ⟨s.val,t.val,s.property,t.property,
        (defect_iff_cellSums small B z hb s t).mpr h⟩

end
end ContingencyTables.SmallGraphProfiles

end OAI
