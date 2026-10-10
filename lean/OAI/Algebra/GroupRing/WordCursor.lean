import Mathlib
import OAI.Algebra.GroupRing.ClosedWords

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordCursor

section
open scoped Classical
variable {A G : Type*} [Group G] (v : A→G)
def value (w : List A) : G := (w.map v).prod
def cursor (w : List A) (n : ℕ) : G := value v (w.take n)
@[simp] lemma value_nil : value v []=1 := rfl
@[simp] lemma value_cons (a : A) (w : List A) : value v (a::w)=v a*value v w := rfl
@[simp] lemma value_append (x y : List A) : value v (x++y)=value v x*value v y := by simp [value]
@[simp] lemma cursor_zero (w : List A) : cursor v w 0=1 := rfl
@[simp] lemma cursor_length (w : List A) : cursor v w w.length=value v w := by simp [cursor]
lemma cursor_succ (w : List A) (i : Fin w.length) :
    cursor v w (i.val+1)=cursor v w i.val*v (w.get i) := by
  rw [cursor,List.take_succ_eq_append_getElem i.isLt,value_append]
  simp only [value_cons,value_nil,mul_one]
  rfl
lemma cursor_append_left (x y : List A) (n : ℕ) (hn : n≤x.length) :
    cursor v (x++y) n=cursor v x n := by
  rw [cursor,List.take_append_of_le_length hn]
  rfl
lemma cursor_append_right (x y : List A) (n : ℕ) :
    cursor v (x++y) (x.length+n)=value v x*cursor v y n := by
  simp only [cursor,List.take_append,List.take_of_length_le (by omega : x.length≤x.length+n),
    Nat.add_sub_cancel_left,value_append]
lemma cursor_cons_succ (a : A) (w : List A) (n : ℕ) :
    cursor v (a::w) (n+1)=v a*cursor v w n := rfl
lemma insert_old (u w : List A) (a b : A) (hb : v a*v b=1) (i : ℕ) :
    cursor v (u++a::b::w) (if i<u.length then i else i+2)=cursor v (u++w) i := by
  by_cases hi : i<u.length
  · rw [ite_eq_left hi,cursor_append_left v u (a::b::w) i hi.le,cursor_append_left v u w i hi.le]
  · rw [ite_eq_right hi]
    have hs : i=u.length+(i-u.length) := by omega
    rw [hs,show u.length+(i-u.length)+2=u.length+((i-u.length)+2) by omega,
      cursor_append_right,cursor_append_right]
    rw [show (i-u.length)+2=((i-u.length)+1)+1 by omega,cursor_cons_succ,cursor_cons_succ]
    calc
      _=value v u*((v a*v b)*cursor v w (i-u.length)) := by simp only [mul_assoc]
      _=_ := by rw [hb,one_mul]
lemma insert_first (u w : List A) (a b : A) : cursor v (u++a::b::w) u.length=value v u := by
  rw [cursor_append_left v u _ _ le_rfl,cursor_length]
lemma insert_second (u w : List A) (a b : A) : cursor v (u++a::b::w) (u.length+1)=value v u*v a := by
  rw [cursor_append_right,cursor_cons_succ,cursor_zero,mul_one]
variable (inv : A→A) (hv : ∀a,v (inv a)=(v a)⁻¹)
def Paired {w : List A} (d : WordPairing.Data inv w.get) : Prop :=
  ∀i,cursor v w (d.partner i).val=cursor v w i.val*v (w.get i)
include hv in
lemma inserted (u w : List A) (a : A) (d : WordPairing.Data inv (u++w).get)
    (ha : inv (inv a)=a) (hd : Paired v inv d) :
    Paired v inv (WordPairing.ListInsert.data u w inv a d ha) := by
  intro i
  let hk : u.length≤(u++w).length := by simp only [List.length_append];omega
  let e := WordPairing.Ear.equiv u.length hk
  obtain ⟨i,rfl⟩ := (WordPairing.ListInsert.orderIso u w inv a).surjective i
  obtain ⟨i,rfl⟩ := e.surjective i
  change cursor v (u++a::inv a::w)
    (((WordPairing.ListInsert.orderIso u w inv a).toEquiv.permCongr
      (WordPairing.Ear.partner u.length d hk)) ((WordPairing.ListInsert.orderIso u w inv a) (e i))).val=_
  simp only [Equiv.permCongr_apply]
  change cursor v (u++a::inv a::w) (WordPairing.Ear.partner u.length d hk (e i)).val=_
  rw [WordPairing.Ear.partner_apply]
  cases i with
  | inl i =>
    change cursor v (u++a::inv a::w) (if (d.partner i).val<u.length then (d.partner i).val else (d.partner i).val+2)=
      cursor v (u++a::inv a::w) (if i.val<u.length then i.val else i.val+2)*
      v ((u++a::inv a::w).get ((WordPairing.ListInsert.orderIso u w inv a) (e (.inl i))))
    rw [insert_old v u w a (inv a) (by rw [hv,mul_inv_cancel]),
      insert_old v u w a (inv a) (by rw [hv,mul_inv_cancel])]
    rw [WordPairing.ListInsert.labels_eq,WordPairing.Ear.labels_left]
    exact hd i
  | inr b =>
    cases b
    · change cursor v (u++a::inv a::w) (u.length+1)=cursor v (u++a::inv a::w) u.length*
        v ((u++a::inv a::w).get ((WordPairing.ListInsert.orderIso u w inv a) (e (.inr false))))
      rw [insert_first,insert_second,WordPairing.ListInsert.labels_eq,WordPairing.Ear.labels_false]
    · change cursor v (u++a::inv a::w) u.length=cursor v (u++a::inv a::w) (u.length+1)*
        v ((u++a::inv a::w).get ((WordPairing.ListInsert.orderIso u w inv a) (e (.inr true))))
      rw [insert_first,insert_second,WordPairing.ListInsert.labels_eq,WordPairing.Ear.labels_true,hv,
        mul_inv_cancel_right]
end
open scoped Classical
variable {A G : Type*} [Group G] (v : A×Bool→G)
  (hv : ∀a,v (WordPairing.inverseLetter a)=(v a)⁻¹)
include hv in
lemma of_reduction {w : List (A×Bool)} (h : FreeGroup.Red w []) :
    ∃d : WordPairing.Data WordPairing.inverseLetter w.get,Paired v _ d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨WordPairing.emptyData,fun i=>Fin.elim0 i⟩
  | @head x y hxy hy ih =>
    cases hxy with
    | @not u w a b =>
      obtain ⟨d,hd⟩ := ih
      exact ⟨WordPairing.ListInsert.data u w WordPairing.inverseLetter (a,b) d
        (WordPairing.inverseLetter_involutive _),inserted v _ hv u w (a,b) d
        (WordPairing.inverseLetter_involutive _) hd⟩
include hv in
lemma of_identity {w : List (A×Bool)} (h : FreeGroup.mk w=1) :
    ∃d : WordPairing.Data WordPairing.inverseLetter w.get,Paired v _ d := by
  apply of_reduction v hv
  have hh : FreeGroup.reduce w=[] := FreeGroup.reduce.sound h
  rw [←hh]
  exact FreeGroup.reduce.red
end TorsionFreeZeroDivisors.WordCursor

end

end OAI
