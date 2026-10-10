import OAI.NumberTheory.Ostmann.Characters.TemplateCore

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

inductive InitialRole (k:ℕ)
  | word
  | pivot (j:Fin k)
  | anchor (j:Fin k) (big:Bool)
  | filler
  deriving DecidableEq, Fintype

def InitialRole.role {k:ℕ} : InitialRole k → Role
  | .word => .word
  | .pivot j => .pivot j.val
  | .anchor j b => .anchor j.val b
  | .filler => .filler

def initial (k:ℕ) : Layout where
  Slot := InitialRole k × Bool
  finite := inferInstance
  role := fun i=>i.1.role
  eligible := fun i=>i.2=true ∧ i.1≠.filler

@[reducible] def schedule (k:ℕ) : ℕ → Layout
  | 0 => initial k
  | j+1 => (schedule k j).step j

theorem initial_word_unique (k:ℕ)
    (z:{i:(initial k).Slot // (initial k).eligible i ∧ (initial k).role i=.word}) :
    z.val=(InitialRole.word,true) := by
  rcases z with ⟨⟨r,b⟩,hz⟩
  have hb : b=true := hz.1.1
  subst b
  have hr : r.role=Role.word := hz.2
  cases r <;> simp_all [InitialRole.role]
  rfl

def wordPathEquiv (k:ℕ) : (j:ℕ) →
    {i:(schedule k j).Slot // (schedule k j).eligible i ∧ (schedule k j).role i=.word} ≃ (Fin j→Bool)
  | 0 =>
    { toFun := fun _ i=>Fin.elim0 i
      invFun := fun _=>⟨(.word,true),by simp [schedule,initial,InitialRole.role]⟩
      left_inv := fun z=>Subtype.ext (initial_word_unique k z).symm
      right_inv := fun f=>by funext i; exact Fin.elim0 i }
  | j+1 => (wordEquiv (schedule k j) j).trans
      ((Equiv.prodCongr (wordPathEquiv k j) (Equiv.refl Bool)).trans
        ((Equiv.prodComm (Fin j→Bool) Bool).trans (Fin.snocEquiv (fun _:Fin (j+1)=>Bool))))

theorem active_word_card (k j:ℕ) :
    Fintype.card {i:(schedule k j).Slot // (schedule k j).eligible i ∧ (schedule k j).role i=.word}=2^j := by
  rw [Fintype.card_congr (wordPathEquiv k j),Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]

theorem initial_pivot_unique (k l:ℕ) (hl:l<k)
    (z:{i:(initial k).Slot // (initial k).IsPivot l i}) :
    z.val=(InitialRole.pivot ⟨l,hl⟩,true) := by
  rcases z with ⟨⟨r,b⟩,hz⟩
  have hb : b=true := hz.1.1
  subst b
  cases r with
  | word => have := hz.2; simp [initial,InitialRole.role] at this
  | filler => exact False.elim (hz.1.2 rfl)
  | anchor j big => have := hz.2; simp [initial,InitialRole.role] at this
  | pivot j =>
    have hj : j.val=l := Role.pivot.inj hz.2
    have he : j=(⟨l,hl⟩:Fin k) := Fin.ext hj
    subst j
    rfl

def pivotEquiv (k:ℕ) : (j l:ℕ) → j≤l → l<k →
    {i:(schedule k j).Slot // (schedule k j).IsPivot l i} ≃ PUnit.{1}
  | 0,l,hjl,hl =>
    { toFun := fun _=>PUnit.unit
      invFun := fun _=>⟨(.pivot ⟨l,hl⟩,true),by simp [schedule,Layout.IsPivot,initial,InitialRole.role]⟩
      left_inv := fun z=>Subtype.ext (initial_pivot_unique k l hl z).symm
      right_inv := fun _=>rfl }
  | j+1,l,hjl,hl => (futurePivotEquiv (schedule k j) j l hjl).trans
      (pivotEquiv k j l (Nat.le_of_succ_le hjl) hl)

def pivotSlot (k j:ℕ) (hj:j<k) : {i:(schedule k j).Slot // (schedule k j).IsPivot j i} :=
  (pivotEquiv k j j le_rfl hj).symm PUnit.unit

theorem pivotSlot_unique (k j:ℕ) (hj:j<k)
    (i:{i:(schedule k j).Slot // (schedule k j).IsPivot j i}) : i=pivotSlot k j hj := by
  apply (pivotEquiv k j j le_rfl hj).injective
  exact Subsingleton.elim _ _

theorem initial_anchor_unique (k l:ℕ) (hl:l<k) (big:Bool)
    (z:{i:(initial k).Slot // (initial k).eligible i ∧ (initial k).role i=.anchor l big}) :
    z.val=(InitialRole.anchor ⟨l,hl⟩ big,true) := by
  rcases z with ⟨⟨r,b⟩,hz⟩
  have hb : b=true := hz.1.1
  subst b
  cases r with
  | word => have := hz.2; simp [initial,InitialRole.role] at this
  | filler => exact False.elim (hz.1.2 rfl)
  | pivot j => have := hz.2; simp [initial,InitialRole.role] at this
  | anchor j c =>
    have hj : j.val=l ∧ c=big := Role.anchor.inj hz.2
    have he : j=(⟨l,hl⟩:Fin k) := Fin.ext hj.1
    subst j
    have hc : c=big := hj.2
    subst c
    rfl

def anchorEquiv (k:ℕ) : (j l:ℕ) → j≤l → (hl:l<k) → (big:Bool) →
    {i:(schedule k j).Slot // (schedule k j).eligible i ∧ (schedule k j).role i=.anchor l big} ≃ PUnit.{1}
  | 0,l,hjl,hl,big =>
    { toFun := fun _=>PUnit.unit
      invFun := fun _=>⟨(.anchor ⟨l,hl⟩ big,true),by simp [schedule,initial,InitialRole.role]⟩
      left_inv := fun z=>Subtype.ext (initial_anchor_unique k l hl big z).symm
      right_inv := fun _=>rfl }
  | j+1,l,hjl,hl,big => (futureAnchorEquiv (schedule k j) j l hjl big).trans
      (anchorEquiv k j l (Nat.le_of_succ_le hjl) hl big)

def anchorSlot (k j:ℕ) (hj:j<k) (big:Bool) :
    {i:(schedule k j).Slot // (schedule k j).eligible i ∧ (schedule k j).role i=.anchor j big} :=
  (anchorEquiv k j j le_rfl hj big).symm PUnit.unit

end Ostmann.Characters.Template

end

end OAI
