import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RayLaurentExpansion

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open FiniteFunctionValues
noncomputable section
abbrev Weak (n : ℕ) := {f : Fin n → ℕ // Monotone f}
abbrev Strict (n : ℕ) := {f : Fin n → ℕ // StrictMono f}

def weakValues (n : ℕ) (f : Weak n) : Sym ℕ n :=
  ⟨values f.val,by rw [values_card,Fintype.card_fin]⟩

lemma weakValues_injective (n : ℕ) : Function.Injective (weakValues n) := by
  intro f g he
  have hm : (List.ofFn f.val:Multiset ℕ)=(List.ofFn g.val:Multiset ℕ) := by
    simpa only [weakValues,values_fin] using congrArg Subtype.val he
  have hf : (List.ofFn f.val).Pairwise (·≤·) := List.pairwise_ofFn.mpr (fun _ _ h=>f.property h.le)
  have hg : (List.ofFn g.val).Pairwise (·≤·) := List.pairwise_ofFn.mpr (fun _ _ h=>g.property h.le)
  have hfg : List.ofFn f.val=List.ofFn g.val := List.Perm.eq_of_pairwise' hf hg (Quotient.exact hm)
  apply Subtype.ext
  exact List.ofFn_inj.mp hfg

lemma weakValues_surjective (n : ℕ) : Function.Surjective (weakValues n) := by
  rintro ⟨m,hm⟩
  let l:=m.sort (·≤·)
  have hl : l.length=n := (Multiset.length_sort (s:=m) (·≤·)).trans hm
  have he : (l:Multiset ℕ)=m := Multiset.sort_eq _ _
  have hp : l.Pairwise (·≤·) := Multiset.pairwise_sort _ _
  cases hl
  refine ⟨⟨l.get,fun _ _ h=>hp.rel_get_of_le h⟩,?_⟩
  apply Subtype.ext
  change values l.get=m
  rw [values_fin,List.ofFn_get]
  exact he

def weakSymEquiv (n : ℕ) : Weak n ≃ Sym ℕ n :=
  Equiv.ofBijective (weakValues n) ⟨weakValues_injective n,weakValues_surjective n⟩

lemma strict_index_le {n : ℕ} (g : Strict n) (i : Fin n) : i.val≤g.val i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have h:=g.property (Fin.castSucc_lt_succ (i:=i))
      change i.val≤g.val i.castSucc at ih
      change i.val+1≤g.val i.succ
      omega

def staircaseEquiv (n : ℕ) : Weak n ≃ Strict n where
  toFun f:=⟨fun i=>f.val i+i.val,by
    intro i j hij
    have h:=f.property hij.le
    have hi : i.val<j.val:=hij
    dsimp only
    omega⟩
  invFun g:=⟨fun i=>g.val i-i.val,by
    cases n with
    | zero => intro i; exact Fin.elim0 i
    | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have h:=g.property (Fin.castSucc_lt_succ (i:=i))
      have hb:=strict_index_le g i.castSucc
      change g.val i.castSucc-i.val≤g.val i.succ-(i.val+1)
      omega⟩
  left_inv f:=by ext i; simp
  right_inv g:=by
    apply Subtype.ext
    funext i
    change g.val i-i.val+i.val=g.val i
    exact Nat.sub_add_cancel (strict_index_le g i)

lemma staircase_sum (n : ℕ) (f : Weak n) :
    (∑i,(staircaseEquiv n f).val i)=(∑i,f.val i)+(∑i:Fin n,i.val) := by
  change (∑ i : Fin n, (f.val i + i.val)) = _
  exact Finset.sum_add_distrib
end
end ElementaryPositivity.UnitSelections
end
end

end OAI
