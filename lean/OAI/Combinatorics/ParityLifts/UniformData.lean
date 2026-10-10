import OAI.Combinatorics.ParityLifts.UniformTags

namespace OAI

namespace ParityWL.Complexity

abbrev RawChoiceData := List (List (List ℕ)) × List (List ℕ)

def ChoiceData.raw {t : ℕ} (D : ChoiceData t) : RawChoiceData :=
  (List.ofFn (fun i => (D.1 i).map List.ofFn),List.ofFn (fun i => List.ofFn (D.2 i)))

def RawChoiceData.entry (D : RawChoiceData) (i d j : ℕ) : ℕ :=
  (((D.1[i]?.getD [])[d]?.getD [])[j]?).getD 0

def RawChoiceData.bound (D : RawChoiceData) (i j : ℕ) : ℕ :=
  ((D.2[min i j]?.getD [])[max i j]?).getD 0

def RawChoiceData.label (D : RawChoiceData) (i d j : ℕ) : ℕ :=
  min (D.entry i d j) (D.bound i j)

lemma ChoiceData.raw_entry {t : ℕ} (D : ChoiceData t) (i : Fin t) (d : ℕ) (j : Fin t) :
    D.raw.entry i.val d j.val=D.entry i d j := by
  simp only [RawChoiceData.entry,raw,List.getElem?_ofFn,Fin.eta]
  cases h : (D.1 i)[d]? with
  | none => simp [h,entry]
  | some row => simp [h,entry,j.isLt]

lemma ChoiceData.raw_bound {t : ℕ} (D : ChoiceData t) (i j : Fin t) :
    D.raw.bound i.val j.val=D.pairBound i j := by
  have hi : min i.val j.val<t := (min_le_left _ _).trans_lt i.isLt
  have hj : max i.val j.val<t := max_lt i.isLt j.isLt
  dsimp only [RawChoiceData.bound,raw,pairBound]
  simp only [List.getElem?_ofFn,hi,hj,↓reduceDIte,Option.getD_some]
  rfl

lemma ChoiceData.raw_label {t : ℕ} (D : ChoiceData t) (i : Fin t) (d : ℕ) (j : Fin t) :
    D.raw.label i.val d j.val=D.label i d j := by
  rw [RawChoiceData.label,D.raw_entry,D.raw_bound]; rfl

def RawChoiceData.roleSize (D : RawChoiceData) (a : RawRole) : ℕ :=
  if a.1=a.2.1 then (D.1[a.1]?.getD []).length else ((D.2[a.1]?.getD [])[a.2.1]?).getD 0+1

lemma ChoiceData.raw_roleSize {t : ℕ} (D : ChoiceData t) (a : TemplateVertex t) :
    D.raw.roleSize (rawRole a)=D.roleSize a := by
  cases a with
  | inl i => simp [RawChoiceData.roleSize,rawRole,raw,roleSize,i.isLt]
  | inr h =>
    have hn : h.1.1.1.1.val≠h.1.1.1.2.val := ne_of_lt h.1.1.2
    dsimp only [RawChoiceData.roleSize,rawRole,raw,roleSize]
    rw [ite_eq_right hn]
    simp [h.1.1.1.1.isLt,h.1.1.1.2.isLt]

def RawChoiceData.helperTest (D : RawChoiceData) (h : RawRole) (q i d : ℕ) : Bool :=
  if i=h.1 then decide (D.label i d h.2.1=q)
  else if i=h.2.1 then decide (D.label i d h.1=q)
  else decide (i=h.2.2)

def RawChoiceData.baseTest (D : RawChoiceData) (a : RawRole) (d : ℕ) (b : RawRole) (e : ℕ) : Bool :=
  if a.1=a.2.1 then
    if b.1=b.2.1 then decide (a.1≠b.1) && decide (D.label a.1 d b.1=D.label b.1 e a.1)
    else D.helperTest b e a.1 d
  else if b.1=b.2.1 then D.helperTest a d b.1 e else false

lemma ChoiceData.raw_helperTest {t : ℕ} (D : ChoiceData t) (h : Helper t) (q : ℕ) (i : Fin t) (d : ℕ) :
    D.raw.helperTest (rawRole (.inr h)) q i.val d=D.helperTest h q i d := by
  dsimp only [RawChoiceData.helperTest,rawRole,helperTest]
  rw [D.raw_label,D.raw_label]
  simp only [Fin.val_inj]

lemma ChoiceData.raw_baseTest {t : ℕ} (D : ChoiceData t) (a b : TemplateVertex t) (d e : ℕ) :
    D.raw.baseTest (rawRole a) d (rawRole b) e=D.baseTest a d b e := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      dsimp only [RawChoiceData.baseTest,rawRole,baseTest]
      simp only [ite_true,D.raw_label]
      congr 2
      exact propext (not_congr Fin.val_inj)
    | inr h =>
      have hn : h.1.1.1.1.val≠h.1.1.1.2.val := ne_of_lt h.1.1.2
      dsimp only [RawChoiceData.baseTest,rawRole,baseTest]
      rw [ite_eq_right hn]
      simpa only [ite_true,rawRole] using D.raw_helperTest h e i d
  | inr h =>
    have hn : h.1.1.1.1.val≠h.1.1.1.2.val := ne_of_lt h.1.1.2
    cases b with
    | inl i =>
      dsimp only [RawChoiceData.baseTest,rawRole,baseTest]
      rw [ite_eq_right hn]
      simpa only [ite_true,rawRole] using D.raw_helperTest h d i e
    | inr g =>
      have gn : g.1.1.1.1.val≠g.1.1.1.2.val := ne_of_lt g.1.1.2
      dsimp only [RawChoiceData.baseTest,rawRole,baseTest]
      rw [ite_eq_right hn,ite_eq_right gn]

end ParityWL.Complexity

end OAI
