import OAI.NumberTheory.Ostmann.Characters.TemplateGraphRegular

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

abbrev Layout.Constituent (T : Layout) (width : Role → ℕ) :=
  Σi:T.Slot,Fin (width (T.role i))

def intraGraph (k : ℕ) : (n : ℕ) → (schedule k n).Slot → ℤ
  | 0 => fun _ => 1
  | n+1 => fun z => match z with
    | .inl (i,t) => copySign t*intraGraph k n i.val
    | .inr _ => 0

def liftGraph (T : Layout) (width : Role → ℕ) (b : T.Slot → T.Slot → ℤ)
    (intra : T.Slot → ℤ) (i h : T.Constituent width) : ℤ :=
  if i=h then 0 else if i.1=h.1 then intra i.1 else b i.1 h.1

def constituentGraph (k n : ℕ) (width : Role → ℕ) :=
  liftGraph (schedule k n) width (graph k n) (intraGraph k n)

theorem constituentGraph_zero (k : ℕ) (width : Role → ℕ)
    (i h : (schedule k 0).Constituent width) (hih : i≠h) :
    constituentGraph k 0 width i h=1 := by
  classical
  simp only [constituentGraph,liftGraph,ite_eq_right hih,intraGraph,graph]
  split_ifs <;> rfl

theorem intraGraph_regular (k : ℕ) : ∀n,∀i:(schedule k n).Slot,
    (schedule k n).IsRegular n i → intraGraph k n i=(rowSign k n i:ℤ) := by
  intro n
  induction n with
  | zero => intro i hi; rfl
  | succ n ih =>
    intro i hi
    obtain ⟨q,t,rfl,hq⟩ := step_regular_cases (schedule k n) n i hi
    simp only [intraGraph,rowSign,Units.val_mul,copyUnit_coe,ih q.val hq]

theorem constituentGraph_regular (k n : ℕ) (hn : n≤k) (width : Role → ℕ)
    (i : (schedule k n).Constituent width) (hi : (schedule k n).IsRegular n i.1)
    (h : (schedule k n).Constituent width) (hhi : h≠i) :
    constituentGraph k n width i h=(rowSign k n i.1:ℤ) := by
  classical
  unfold constituentGraph liftGraph
  rw [ite_eq_right hhi.symm]
  split_ifs with he
  · exact intraGraph_regular k n i.1 hi
  · exact graph_regular k n hn i.1 hi h.1 (Ne.symm he)

theorem liftGraph_pivot_column (T : Layout) (width : Role → ℕ)
    (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ)
    (i : T.Constituent width) (p : T.Slot) (hip : i.1≠p)
    (a : Fin (width (T.role p))) : liftGraph T width b intra i ⟨p,a⟩=b i.1 p := by
  classical
  have hi : i≠⟨p,a⟩ := fun he => hip (congrArg Sigma.fst he)
  simp only [liftGraph,ite_eq_right hi,ite_eq_right hip]

abbrev CopiedConstituent (T : Layout) (j : ℕ) (width : Role → ℕ) :=
  Σi:{i:T.Slot // T.IsCopied j i},Fin (width (T.role i.val))

abbrev OutsideConstituent (T : Layout) (j : ℕ) (width : Role → ℕ) :=
  Σi:{i:T.Slot // T.IsOutside j i},Fin (width (T.role i.val))

def nextConstituentEquiv (T : Layout) (j : ℕ) (width : Role → ℕ) :
    (T.step j).Constituent width ≃
      (CopiedConstituent T j width × Bool) ⊕ OutsideConstituent T j width where
  toFun x := match x with
    | ⟨.inl (i,t),a⟩ => .inl (⟨i,a⟩,t)
    | ⟨.inr i,a⟩ => .inr ⟨i,a⟩
  invFun x := match x with
    | .inl (⟨i,a⟩,t) => ⟨.inl (i,t),a⟩
    | .inr ⟨i,a⟩ => ⟨.inr i,a⟩
  left_inv x := by rcases x with ⟨x,a⟩; cases x <;> rfl
  right_inv x := by
    cases x with
    | inl x => rcases x with ⟨⟨i,a⟩,t⟩; rfl
    | inr x => rcases x with ⟨i,a⟩; rfl

def copiedConstituentOld (T : Layout) (j : ℕ) (width : Role → ℕ)
    (i : CopiedConstituent T j width) : T.Constituent width := ⟨i.1.val,i.2⟩
def outsideConstituentOld (T : Layout) (j : ℕ) (width : Role → ℕ)
    (i : OutsideConstituent T j width) : T.Constituent width := ⟨i.1.val,i.2⟩

def collapsedConstituentGraph (T : Layout) (j : ℕ) (width : Role → ℕ)
    (p : {i:T.Slot // T.IsPivot j i}) (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ) :
    Option (CopiedConstituent T j width ⊕ OutsideConstituent T j width) →
      Option (CopiedConstituent T j width ⊕ OutsideConstituent T j width) → ℤ
  | none,none => 0
  | none,some (.inl i) => b p.val i.1.val
  | none,some (.inr i) => b p.val i.1.val
  | some (.inl i),none => b i.1.val p.val
  | some (.inr i),none => b i.1.val p.val
  | some (.inl i),some (.inl h) =>
      liftGraph T width b intra (copiedConstituentOld T j width i) (copiedConstituentOld T j width h)
  | some (.inl i),some (.inr h) =>
      liftGraph T width b intra (copiedConstituentOld T j width i) (outsideConstituentOld T j width h)
  | some (.inr i),some (.inl h) =>
      liftGraph T width b intra (outsideConstituentOld T j width i) (copiedConstituentOld T j width h)
  | some (.inr i),some (.inr h) =>
      liftGraph T width b intra (outsideConstituentOld T j width i) (outsideConstituentOld T j width h)

end Ostmann.Characters.Template

end

end OAI
