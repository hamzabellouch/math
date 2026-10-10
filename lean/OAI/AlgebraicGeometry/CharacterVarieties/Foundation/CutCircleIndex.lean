import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

namespace OAI

noncomputable section
open scoped Classical

namespace IntegralCharacterVarieties.CutCircleIndex
open scoped Classical
variable {F G : Type} (n : F → ℕ) (p : F)
def extra (f : F) : ℕ := if f=p then 1 else 0
def count : F ⊕ G → ℕ := Sum.elim (fun f => n f+extra p f) (fun _ => 1)
abbrev Label := ((f : F) × Fin (n f)) ⊕ (Unit ⊕ G)
def selected : ((f : F) × Fin (extra p f)) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨p,⟨0,by simp [extra]⟩⟩
  left_inv := by
    rintro ⟨f,i⟩
    have h : f=p := by
      by_contra hn
      have hi := i.isLt
      simp [extra,hn] at hi
    subst f
    have he : (⟨0,by simp [extra]⟩ : Fin (extra p p))=i := by
      apply Fin.ext
      have hi := i.isLt
      have hh : extra p p=1 := by simp [extra]
      have hz : i.val < 1 := lt_of_lt_of_le hi hh.le
      change 0=i.val
      omega
    exact congrArg (fun j : Fin (extra p p) => (⟨p,j⟩ : (f : F) × Fin (extra p f))) he
  right_inv _ := rfl

def oldPart : ((f : F) × Fin (n f+extra p f)) ≃ (((f : F) × Fin (n f)) ⊕ Unit) :=
  (Equiv.sigmaCongrRight (fun _ => finSumFinEquiv.symm)).trans
    ((Equiv.sigmaSumDistrib (fun f => Fin (n f)) (fun f => Fin (extra p f))).trans
      (Equiv.sumCongr (Equiv.refl _) (selected p)))

/-- Indexed boundary order: all old circles remain in their old order, the single mirror circle is appended at the selected parent, and every newly created strip disk has exactly one boundary. -/
def enumeration : ((f : F ⊕ G) × Fin (count (G:=G) n p f)) ≃ Label (G:=G) n :=
  (Equiv.sumSigmaDistrib (fun f => Fin (count n p f))).trans
    ((Equiv.sumCongr (oldPart n p) (Equiv.sigmaUnique G (fun _ => Fin 1))).trans
      (Equiv.sumAssoc _ _ _))
lemma enumeration_old (f : F) (i : Fin (n f)) :
    enumeration (G:=G) n p ⟨.inl f,i.castAdd (extra p f)⟩=.inl ⟨f,i⟩ := by
  change (Equiv.sumAssoc _ _ _) (.inl (oldPart n p ⟨f,i.castAdd (extra p f)⟩))=_
  simp only [oldPart,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,
    finSumFinEquiv_symm_apply_castAdd]
  rfl
lemma enumeration_mirror :
    enumeration (G:=G) n p ⟨.inl p,⟨n p,by simp [count,extra]⟩⟩=.inr (.inl ()) := by
  change (Equiv.sumAssoc _ _ _) (.inl (oldPart n p ⟨p,⟨n p,_⟩⟩))=_
  have he : (⟨n p,by simp [extra]⟩ : Fin (n p+extra p p))=Fin.natAdd (n p) ⟨0,by simp [extra]⟩ := rfl
  rw [he]
  simp only [oldPart,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,finSumFinEquiv_symm_apply_natAdd]
  rfl
lemma enumeration_fresh (g : G) :
    enumeration n p ⟨.inr g,⟨0,by exact Nat.zero_lt_one⟩⟩=.inr (.inr g) := rfl
end IntegralCharacterVarieties.CutCircleIndex

end

end OAI
