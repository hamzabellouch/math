import OAI.NumberTheory.Ostmann.Characters.TemplateGraphRegular

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

abbrev Word (k n : ℕ) :=
  {i:(schedule k n).Slot // (schedule k n).eligible i ∧ (schedule k n).role i=.word}

def anchorCopied (k n : ℕ) (hn : n<k) (big : Bool) :
    {i:(schedule k n).Slot // (schedule k n).IsCopied n i} :=
  ⟨(anchorSlot k n hn big).val,(anchorSlot k n hn big).property.1,
    Or.inr (Or.inr ⟨big,(anchorSlot k n hn big).property.2⟩)⟩

def freshAnchor (k n : ℕ) (hn : n<k) (big t : Bool) :
    {i:(schedule k (n+1)).Slot // ¬(schedule k (n+1)).eligible i ∧
      (schedule k (n+1)).role i=.anchor n big} :=
  ⟨.inl (anchorCopied k n hn big,t),by
    constructor
    · rintro (hw | ⟨l,hp,_⟩)
      · have he := (anchorSlot k n hn big).property.2.symm.trans hw
        contradiction
      · have he := (anchorSlot k n hn big).property.2.symm.trans hp
        contradiction
    · exact (anchorSlot k n hn big).property.2⟩

def carryRetired (T : Layout) (n l : ℕ) (big : Bool)
    (i : {i:T.Slot // ¬T.eligible i ∧ T.role i=.anchor l big}) :
    {i:(T.step n).Slot // ¬(T.step n).eligible i ∧ (T.step n).role i=.anchor l big} :=
  ⟨.inr ⟨i.val,fun h => i.property.1 h.1,fun h => i.property.1 h.1⟩,i.property⟩

def retiredAnchors (k : ℕ) : (n : ℕ) → n≤k → (big : Bool) → (j : Fin n) → Bool →
    {i:(schedule k n).Slot // ¬(schedule k n).eligible i ∧
      (schedule k n).role i=.anchor j.val big}
  | 0,_,_,j => Fin.elim0 j
  | n+1,hn,big,j => Fin.lastCases (fun t => freshAnchor k n hn big t)
      (fun j t => carryRetired (schedule k n) n j.val big
        (retiredAnchors k n (by omega) big j t)) j

def pathSigns (k : ℕ) : (n : ℕ) → Word k n → AnchorCodes.ParityPath n
  | 0,_ => fun _ => 1
  | n+1,w => Fin.snoc (pathSigns k n ((wordEquiv (schedule k n) n) w).1)
      (rowSign k (n+1) w.val)

@[simp] theorem pathSigns_last (k n : ℕ) (w : Word k n) :
    pathSigns k n w (Fin.last n)=rowSign k n w.val := by
  cases n with
  | zero => rfl
  | succ n => simp only [pathSigns,Fin.snoc_last]

@[simp] theorem pathSigns_castSucc (k n : ℕ) (w : Word k (n+1)) (j : Fin (n+1)) :
    pathSigns k (n+1) w j.castSucc =
      pathSigns k n ((wordEquiv (schedule k n) n) w).1 j := by
  simp only [pathSigns,Fin.snoc_castSucc]

theorem rowSign_word_step (k n : ℕ) (w : Word k (n+1)) :
    rowSign k (n+1) w.val = copyUnit ((wordEquiv (schedule k n) n) w).2 *
      rowSign k n ((wordEquiv (schedule k n) n) w).1.val := by
  rcases w with ⟨w,hw⟩
  cases w with
  | inl q => rfl
  | inr q => exact False.elim (q.property.2 (word_copied _ _ _ hw.1 hw.2))

theorem copyUnit_injective : Function.Injective copyUnit := by
  intro t u h
  cases t <;> cases u <;> simp_all [copyUnit]

theorem pathSigns_injective (k : ℕ) : ∀n,Function.Injective (pathSigns k n) := by
  intro n
  induction n with
  | zero =>
    intro w z h
    apply Subtype.ext
    exact (initial_word_unique k w).trans (initial_word_unique k z).symm
  | succ n ih =>
    intro w z h
    apply (wordEquiv (schedule k n) n).injective
    have hold : ((wordEquiv (schedule k n) n) w).1=((wordEquiv (schedule k n) n) z).1 := by
      apply ih
      funext j
      simpa only [pathSigns_castSucc] using congrFun h j.castSucc
    refine Prod.ext hold ?_
    apply copyUnit_injective
    have hh := congrFun h (Fin.last (n+1))
    rw [pathSigns_last,pathSigns_last,rowSign_word_step,rowSign_word_step,hold] at hh
    exact mul_right_cancel hh

theorem actual_code_final_injective (k n : ℕ) :
    Function.Injective (fun w : Word k n =>
      (AnchorCodes.code (fun _ => 1) (pathSigns k n w),rowSign k n w.val)) := by
  intro w z h
  apply pathSigns_injective k n
  apply AnchorCodes.code_final_injective (fun _ => 1)
  simpa only [pathSigns_last] using h

end Ostmann.Characters.Template

end

end OAI
