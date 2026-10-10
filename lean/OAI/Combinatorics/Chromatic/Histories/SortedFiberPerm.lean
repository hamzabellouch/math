import Mathlib

namespace OAI

section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {B:Type*} [DecidableEq B]

def fiber (f:Fin n → B) (b:B) : Finset (Fin n):=Finset.univ.filter (fun i=>f i=b)
def card (f:Fin n → B) (b:B):= (fiber f b).card
@[simp] lemma mem_fiber (f:Fin n → B) (b:B) (i:Fin n) : i∈fiber f b ↔ f i=b:=by simp [fiber]
lemma card_eq (f:Fin n → B) (b:B) : card f b=Fintype.card {i // f i=b}:=by simp [card,fiber,Fintype.card_subtype]

def fiberOrder (f:Fin n → B) (b:B) {k:ℕ} (h:card f b=k) : Fin k ≃o {i // f i=b}:=
  ((fiber f b).orderIsoOfFin h).trans
    (Set.orderIsoOfEq {i | i∈fiber f b} {i | f i=b} (by ext i; simp))

def fiberIso (f g:Fin n → B) (h:∀b,card f b=card g b) (b:B) :
    {i // f i=b} ≃o {i // g i=b}:=
  (fiberOrder f b rfl).symm.trans (fiberOrder g b (h b).symm)

def sortedPerm (f g:Fin n → B) (h:∀b,card f b=card g b) : Equiv.Perm (Fin n):=
  Equiv.ofFiberEquiv (fun b=>(fiberIso f g h b).toEquiv)
lemma sortedPerm_map (f g:Fin n → B) (h:∀b,card f b=card g b) (i:Fin n) :
    g (sortedPerm f g h i)=f i:=Equiv.ofFiberEquiv_map _ _

def Sorted {A:Type*} [LT A] (f:Fin n → B) (w:Fin n → A) : Prop:=
  ∀i j,f i=f j → i<j → w i<w j
lemma sortedPerm_sorted (f g:Fin n → B) (h:∀b,card f b=card g b) :
    Sorted f (sortedPerm f g h) := by
  intro i j hij hlt
  change (fiberIso f g h (f i) ⟨i,rfl⟩).val <
    (fiberIso f g h (f j) ⟨j,rfl⟩).val
  have hj: (fiberIso f g h (f j) ⟨j,rfl⟩).val=
      (fiberIso f g h (f i) ⟨j,hij.symm⟩).val:=by
    have aux:∀b (hb:f j=b), (fiberIso f g h (f j) ⟨j,rfl⟩).val=
        (fiberIso f g h b ⟨j,hb⟩).val:=by
      intro b hb
      subst b
      rfl
    exact aux _ hij.symm
  rw [hj]
  exact (fiberIso f g h (f i)).strictMono hlt

omit [DecidableEq B] in
lemma sorted_unique (f g:Fin n → B) (w v:Equiv.Perm (Fin n))
    (hw:∀i,g (w i)=f i) (hv:∀i,g (v i)=f i)
    (hsw:Sorted f w) (hsv:Sorted f v) : w=v := by
  let e (u:Equiv.Perm (Fin n)) (hu:∀i,g (u i)=f i) (hs:Sorted f u) (b:B) :
      {i // f i=b} ≃o {i // g i=b}:=
    StrictMono.orderIsoOfSurjective (fun i=>⟨u i,by rw [hu,i.property]⟩)
      (fun i j hij=>hs i j (i.property.trans j.property.symm) hij)
      (by
        intro j
        refine ⟨⟨u.symm j,?_⟩,?_⟩
        · rw [←hu,u.apply_symm_apply]; exact j.property
        · exact Subtype.ext (u.apply_symm_apply j))
  apply Equiv.ext
  intro i
  have H:e w hw hsw (f i)=e v hv hsv (f i):=Subsingleton.elim _ _
  exact congrArg (fun q=> (q ⟨i,rfl⟩).val) H

lemma card_of_perm (f g:Fin n → B) (w:Equiv.Perm (Fin n)) (hw:∀i,g (w i)=f i) :
    ∀b,card f b=card g b := by
  intro b
  rw [card_eq,card_eq]
  exact Fintype.card_congr (w.subtypeEquiv (fun i=>by rw [hw]))
end
end ElementaryPositivity.Packets

end
section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def left (t:Fin (n-1)):Fin n:=⟨t.val,by omega⟩
def right (t:Fin (n-1)):Fin n:=⟨t.val+1,by omega⟩
def ascentMask {A:Type*} (R:A → A → Prop) (w:Fin n → A) : Finset (Fin (n-1)):=
  Finset.univ.filter (fun t=>R (w (left t)) (w (right t)))
@[simp] lemma mem_ascentMask {A:Type*} (R:A → A → Prop) (w:Fin n → A) (t:Fin (n-1)) :
    t∈ascentMask R w ↔ R (w (left t)) (w (right t)):=by simp [ascentMask]

def gap (J:Finset (Fin (n-1))) (k:ℕ) : ℕ:=if k∈J.image Fin.val then 0 else 1
def indexVal (J:Finset (Fin (n-1))) (k:ℕ) : ℕ:=∑t∈Finset.range k,gap J t
lemma indexVal_succ (J:Finset (Fin (n-1))) (k:ℕ) :
    indexVal J (k+1)=indexVal J k+gap J k:=by simp [indexVal,Finset.sum_range_succ]
lemma indexVal_mono (J:Finset (Fin (n-1))) : Monotone (indexVal J):=by
  apply monotone_nat_of_le_succ
  intro k
  rw [indexVal_succ]
  omega
lemma indexVal_le (J:Finset (Fin (n-1))) (k:ℕ) : indexVal J k≤k:=by
  induction k with
  | zero=>simp [indexVal]
  | succ k ih=>rw [indexVal_succ]; unfold gap; split_ifs <;> omega

def index (J:Finset (Fin (n-1))) (i:Fin n):Fin (n+1):=
  ⟨indexVal J i.val,by have H:=indexVal_le J i.val; omega⟩
lemma index_mono (J:Finset (Fin (n-1))) : Monotone (index J):=by
  intro i j hij
  exact indexVal_mono J hij
lemma index_adjacent (J:Finset (Fin (n-1))) (i j:Fin n) (h:i.val+1=j.val) :
    index J i=index J j ↔ (⟨i.val,by omega⟩:Fin (n-1))∈J := by
  rw [Fin.ext_iff]
  change indexVal J i.val=indexVal J j.val ↔ _
  rw [←h,indexVal_succ]
  have hm:i.val∈J.image Fin.val ↔ (⟨i.val,by omega⟩:Fin (n-1))∈J:=by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨t,ht,he⟩
      have H:t=⟨i.val,by omega⟩:=Fin.ext he
      simpa only [←H] using ht
    · intro ht
      exact ⟨⟨i.val,by omega⟩,ht,rfl⟩
  simp only [gap,hm]
  split_ifs <;> simp_all
lemma index_left_right (J:Finset (Fin (n-1))) (t:Fin (n-1)) :
    index J (left t)=index J (right t) ↔ t∈J := by
  exact index_adjacent J _ _ rfl

lemma inside_of_required {A:Type*} (R:A → A → Prop)
    (hR:∀ ⦃first middle last : A⦄, R first middle → R middle last → R first last)
    (J:Finset (Fin (n-1))) (w:Fin n → A) (hw:J⊆ascentMask R w)
    (i j:Fin n) (hij:i<j) (he:index J i=index J j) : R (w i) (w j) := by
  cases n with
  | zero=>exact Fin.elim0 i
  | succ N=>
    have H:∀j:Fin (N+1),∀i:Fin (N+1),i<j → index J i=index J j → R (w i) (w j):=by
      intro j
      induction j using Fin.induction with
      | zero=>intro i hi; exact (not_lt_of_ge (Fin.zero_le i) hi).elim
      | succ k ih=>
        intro i hij he
        have hk:index J k.castSucc=index J k.succ:=by
          apply le_antisymm
          · exact index_mono J (by simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
          · rw [←he]
            exact index_mono J (by
              change i.val≤k.val
              change i.val<k.val+1 at hij
              omega)
        have hm:(⟨k.val,by omega⟩:Fin ((N+1)-1))∈J:=
          (index_adjacent J k.castSucc k.succ rfl).mp hk
        have hr:R (w k.castSucc) (w k.succ):=by
          exact (mem_ascentMask R w _).mp (hw hm)
        by_cases hik:i=k.castSucc
        · simpa only [hik] using hr
        · have hiv:i.val≠k.val:=fun H=>hik (Fin.ext H)
          have hit:i<k.castSucc:=by
            change i.val<k.val
            change i.val<k.val+1 at hij
            omega
          exact hR (ih i hit (he.trans hk.symm)) hr
    exact H j i hij he
end
end ElementaryPositivity.Packets

end

end OAI
