import OAI.NumberTheory.Ostmann.Characters.BinaryHaar
import OAI.NumberTheory.Ostmann.Characters.TemplateHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template

abbrev WordSlot (k j:ℕ) :=
  {i:(schedule k j).Slot // (schedule k j).eligible i ∧ (schedule k j).role i=.word}

def wordAssignmentSplit {G:Type*} (k j:ℕ) :
    (WordSlot k (j+1)→G) ≃ (WordSlot k j→G)×(WordSlot k j→G) where
  toFun f := (fun i=>f ((wordEquiv (schedule k j) j).symm (i,true)),
    fun i=>f ((wordEquiv (schedule k j) j).symm (i,false)))
  invFun g := fun i=>if (wordEquiv (schedule k j) j i).2 then
    g.1 (wordEquiv (schedule k j) j i).1 else g.2 (wordEquiv (schedule k j) j i).1
  left_inv f := by
    funext i
    have h := (wordEquiv (schedule k j) j).symm_apply_apply i
    generalize he:(wordEquiv (schedule k j) j) i=z at *
    rcases z with ⟨i,b⟩
    cases b <;> simpa only [he,Prod.fst,Prod.snd,Bool.false_eq_true,ite_false,ite_true] using congrArg f h
  right_inv g := by
    apply Prod.ext <;> funext i <;> simp only [Equiv.apply_symm_apply,ite_true,Bool.false_eq_true,ite_false]

def wordTreeEquiv {G:Type*} (k:ℕ) : (j:ℕ)→(WordSlot k j→G) ≃ BinaryHaar.Leaves G j
  | 0 =>
    { toFun := fun f=>f ⟨(.word,true),by simp [schedule,initial,InitialRole.role]⟩
      invFun := fun x _=>x
      left_inv := fun f=>by
        funext i
        apply congrArg f
        apply Subtype.ext
        exact (initial_word_unique k i).symm
      right_inv := fun _=>rfl }
  | j+1 => (wordAssignmentSplit k j).trans
      (Equiv.prodCongr (wordTreeEquiv k j) (wordTreeEquiv k j))

def wordLeaves (k j:ℕ) (x:State k j) : BinaryHaar.Leaves ℤ j :=
  wordTreeEquiv (G:=ℤ) k j (fun i=>x i.val)

theorem wordLeaves_left (k j:ℕ) (x:State k (j+1)) (P:ℤ) :
    (wordLeaves k (j+1) x).1=wordLeaves k j (childState k j true x P) := by
  change wordTreeEquiv (G:=ℤ) k j _=wordTreeEquiv (G:=ℤ) k j _
  apply congrArg (wordTreeEquiv (G:=ℤ) k j)
  funext i
  exact (childState_copied k j true x P
    ⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩).symm

theorem wordLeaves_right (k j:ℕ) (x:State k (j+1)) (P:ℤ) :
    (wordLeaves k (j+1) x).2=wordLeaves k j (childState k j false x P) := by
  change wordTreeEquiv (G:=ℤ) k j _=wordTreeEquiv (G:=ℤ) k j _
  apply congrArg (wordTreeEquiv (G:=ℤ) k j)
  funext i
  exact (childState_copied k j false x P
    ⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩).symm

def flattenLeaves {G:Type*} : (j:ℕ)→BinaryHaar.Leaves G j→List G
  | 0,x => [x]
  | j+1,x => flattenLeaves j x.1 ++ flattenLeaves j x.2

def originalWord (k:ℕ) (x:State k 0) : ℤ := x (.word,true)

theorem leafStates_words (k j:ℕ) (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j) :
    (leafStates k j s x t).map (fun z=>originalWord k z.2)=flattenLeaves j (wordLeaves k j x) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    simp only [leafStates,List.map_append,ih,flattenLeaves]
    rw [wordLeaves_left k j x (reconstructedPivot k j x s t.1.1 t.1.2),
      wordLeaves_right k j x (reconstructedPivot k j x s t.1.1 t.1.2)]

end Ostmann.Characters.Template

end

end OAI
