import OAI.NumberTheory.Ostmann.Characters.SourceTemplateDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate

def listOccurrenceCons {α : Type*} (a : List α) (ls : List (List α)) :
    (Σ i : Fin (a::ls).length, Fin ((a::ls).get i).length) ≃
      Fin a.length ⊕ (Σ i : Fin ls.length, Fin (ls.get i).length) where
  toFun x := Fin.cases (fun j => Sum.inl j) (fun i j => Sum.inr ⟨i,j⟩) x.1 x.2
  invFun
    | .inl j => ⟨0,j⟩
    | .inr ⟨i,j⟩ => ⟨i.succ,j⟩
  left_inv x := by
    rcases x with ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i j
    · intro j; rfl
    · intro j; rfl
  right_inv x := by cases x <;> rfl

def listFlattenPositionEquiv {α : Type*} : (ls : List (List α)) →
    (Σ i : Fin ls.length, Fin (ls.get i).length) ≃ Fin ls.flatten.length
  | [] =>
    { toFun := fun x => Fin.elim0 x.1
      invFun := Fin.elim0
      left_inv := fun x => Fin.elim0 x.1
      right_inv := fun x => Fin.elim0 x }
  | a::ls =>
    (listOccurrenceCons a ls).trans
      ((Equiv.sumCongr (Equiv.refl _) (listFlattenPositionEquiv ls)).trans
        (finSumFinEquiv.trans (finCongr (by simp only [List.flatten_cons, List.length_append]))))

theorem listFlattenPositionEquiv_get {α : Type*} (ls : List (List α))
    (x : Σ i : Fin ls.length, Fin (ls.get i).length) :
    ls.flatten.get (listFlattenPositionEquiv ls x) = (ls.get x.1).get x.2 := by
  induction ls with
  | nil => exact Fin.elim0 x.1
  | cons a ls ih =>
    rcases x with ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i j
    · intro j
      change (a ++ ls.flatten)[j.val] = a[j.val]
      exact List.getElem_append_left j.isLt
    · intro j
      have hvalid : a.length + (listFlattenPositionEquiv ls ⟨i,j⟩).val < (a ++ ls.flatten).length := by
        simpa only [List.length_append] using Nat.add_lt_add_left (listFlattenPositionEquiv ls ⟨i,j⟩).isLt a.length
      change (a ++ ls.flatten)[a.length + (listFlattenPositionEquiv ls ⟨i,j⟩).val] = (ls.get i).get j
      rw [List.getElem_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem] using ih ⟨i,j⟩

def roleListPositionEquiv {k : ℕ} (cfg : SourceConfiguration k) :
    (Σ j : Fin (k+1), Fin (cfg.2 j).length) ≃ Fin (List.ofFn cfg.2).flatten.length :=
  ((finCongr (List.length_ofFn (f := cfg.2)).symm).sigmaCongr
    (fun j => finCongr (by simp only [List.get_eq_getElem, List.getElem_ofFn, finCongr_apply, Fin.val_cast]))).trans
    (listFlattenPositionEquiv (List.ofFn cfg.2))

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
