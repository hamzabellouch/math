import OAI.Computability.WeisfeilerLeman.Predicates

namespace OAI

universe uJ

namespace WLTime.Digits

abbrev Word (d m : ℕ) := Fin d → Fin m
abbrev encode {d m : ℕ} : Word d m ≃ Fin (m^d) := finFunctionFinEquiv

def value {d m : ℕ} (a : Word d m) : ℕ := (encode a).val

@[simp] theorem value_zero {m : ℕ} (a : Word 0 m) : value a = 0 := by
  simp [value,encode]

theorem value_succ {d m : ℕ} (a : Word (d+1) m) :
    value a = (a 0).val + m * value (fun i : Fin d => a i.succ) := by
  simp only [value,encode,finFunctionFinEquiv_apply,Fin.sum_univ_succ,
    Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def CarryDomain {d m : ℕ} (p : Fin (d+1)) (i : Fin d) : Finset (Fin m) :=
  Finset.univ.filter fun x => if i.val < p.val then x.val+1=m
    else if i.val=p.val then x.val + 1 < m else True

def Allowed {d m : ℕ} (p : Fin (d+1)) (a : Word d m) : Prop :=
  ∀ i, a i ∈ CarryDomain p i

theorem allowed_iff {d m : ℕ} (p : Fin (d+1)) (a : Word d m) :
    Allowed p a ↔ ∀ i, if i.val < p.val then (a i).val+1=m
      else if i.val=p.val then (a i).val + 1 < m else True := by
  simp only [Allowed,CarryDomain,Finset.mem_filter,Finset.mem_univ,true_and]

def inc (m : ℕ) : Equiv.Perm (Fin m) := finRotate m

def coordinate {d m : ℕ} (p : Fin (d+1)) (i : Fin d) : Equiv.Perm (Fin m) :=
  if i.val ≤ p.val then inc m else Equiv.refl _

def applyCarry {d m : ℕ} (p : Fin (d+1)) (a : Word d m) : Word d m :=
  fun i => coordinate p i (a i)

theorem inc_value {m : ℕ} (x : Fin m) :
    (inc m x).val = if x.val + 1 = m then 0 else x.val + 1 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt x.pos)
  rw [inc,coe_finRotate]
  have he : x=Fin.last m ↔ x.val+1=m+1 := by
    simp only [Fin.ext_iff,Fin.val_last]
    omega
  simp only [he]

theorem allowed_zero {d m : ℕ} (a : Word (d+1) m) :
    Allowed (0 : Fin (d+2)) a ↔ (a 0).val + 1 < m := by
  simp [allowed_iff]

theorem allowed_succ {d m : ℕ} (p : Fin (d+1)) (a : Word (d+1) m) :
    Allowed p.succ a ↔ (a 0).val+1=m ∧ Allowed p (fun i => a i.succ) := by
  rw [allowed_iff,Fin.forall_fin_succ,allowed_iff]
  simp only [Fin.val_zero,Fin.val_succ,Nat.zero_lt_succ,ite_true,
    Nat.add_lt_add_iff_right,Nat.add_right_cancel_iff]

@[simp] theorem apply_zero_head {d m : ℕ} (a : Word (d+1) m) :
    applyCarry (0 : Fin (d+2)) a 0 = inc m (a 0) := by
  simp [applyCarry,coordinate]

@[simp] theorem apply_zero_tail {d m : ℕ} (a : Word (d+1) m) (i : Fin d) :
    applyCarry (0 : Fin (d+2)) a i.succ = a i.succ := by
  simp [applyCarry,coordinate]

@[simp] theorem apply_succ_head {d m : ℕ} (p : Fin (d+1)) (a : Word (d+1) m) :
    applyCarry p.succ a 0 = inc m (a 0) := by
  simp [applyCarry,coordinate]

@[simp] theorem apply_succ_tail {d m : ℕ} (p : Fin (d+1)) (a : Word (d+1) m) (i : Fin d) :
    applyCarry p.succ a i.succ = applyCarry p (fun i => a i.succ) i := by
  simp [applyCarry,coordinate]

theorem exists_allowed {d m : ℕ} (a : Word d m) : ∃ p : Fin (d+1), Allowed p a := by
  induction d with
  | zero => exact ⟨0,fun i => Fin.elim0 i⟩
  | succ d ih =>
    by_cases hm : (a 0).val+1=m
    · obtain ⟨p,hp⟩ := ih (fun i => a i.succ)
      exact ⟨p.succ,(allowed_succ p a).mpr ⟨hm,hp⟩⟩
    · exact ⟨0,(allowed_zero a).mpr (by have := (a 0).isLt; omega)⟩

theorem carry_value {d m : ℕ} (p : Fin (d+1)) (a : Word d m) (ha : Allowed p a) :
    value (applyCarry p a) = if p.val=d then 0 else value a+1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    revert ha
    refine Fin.cases ?_ (fun p => ?_) p
    · intro ha
      have ha0 : (a 0).val+1< m := (allowed_zero a).mp ha
      simp only [Fin.val_zero,Ne.symm (Nat.succ_ne_zero d),ite_false]
      rw [value_succ,value_succ,apply_zero_head,inc_value]
      simp only [apply_zero_tail,ite_eq_right (Nat.ne_of_lt ha0)]
      omega
    · intro ha
      obtain ⟨ha0,hat⟩ := (allowed_succ p a).mp ha
      have ht := ih p (fun i => a i.succ) hat
      rw [value_succ,value_succ,apply_succ_head,inc_value,ite_eq_left ha0]
      simp only [apply_succ_tail,Fin.val_succ,Nat.add_right_cancel_iff]
      rw [ht]
      split_ifs with hp
      · simp
      · nlinarith

theorem wrap_value {d m : ℕ} (a : Word d m) (ha : Allowed (Fin.last d) a) :
    value a+1=m^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh : Fin.last (d+1) = (Fin.last d).succ := rfl
    rw [hh,allowed_succ] at ha
    obtain ⟨ha0,hat⟩ := ha
    have ht := ih (fun i => a i.succ) hat
    rw [value_succ,pow_succ]
    nlinarith

theorem carry_rotation {d m : ℕ} (p : Fin (d+1)) (a : Word d m) (ha : Allowed p a) :
    encode (applyCarry p a) = inc (m^d) (encode a) := by
  apply Fin.ext
  change value (applyCarry p a) = _
  rw [inc_value]
  change value (applyCarry p a) = if value a+1=m^d then 0 else value a+1
  rw [carry_value p a ha]
  by_cases hp : p.val=d
  · have he : p=Fin.last d := Fin.ext hp
    have hv := wrap_value a (he ▸ ha)
    simp only [hp,hv,ite_true]
  · have hv : value a+1 < m^d := by
      have hb := (encode (applyCarry p a)).isLt
      change value (applyCarry p a) < m^d at hb
      simpa only [carry_value p a ha,ite_eq_right hp] using hb
    simp only [ite_eq_right hp,ite_eq_right (Nat.ne_of_lt hv)]

theorem carry_relation {d m : ℕ} (a b : Word d m) :
    (∃ p : Fin (d+1), Allowed p a ∧ applyCarry p a=b) ↔
      encode b=inc (m^d) (encode a) := by
  constructor
  · rintro ⟨p,ha,rfl⟩
    exact carry_rotation p a ha
  · intro hab
    obtain ⟨p,ha⟩ := exists_allowed a
    refine ⟨p,ha,encode.injective ?_⟩
    exact (carry_rotation p a ha).trans hab.symm

theorem nonwrap_relation {d m : ℕ} (a b : Word d m) :
    (∃ p : Fin d, Allowed p.castSucc a ∧ applyCarry p.castSucc a=b) ↔
      value b=value a+1 := by
  constructor
  · rintro ⟨p,ha,rfl⟩
    rw [carry_value p.castSucc a ha]; simp only [Fin.val_castSucc,ite_eq_right (Nat.ne_of_lt p.isLt)]
  · intro hab
    obtain ⟨p,ha⟩ := exists_allowed a
    have hp : p.val<d := by
      have hv : value b< m^d := (encode b).isLt
      have hlt := p.isLt
      by_contra hn
      have he : p=Fin.last d := Fin.ext (by simp only [Fin.val_last]; omega)
      have hw := wrap_value a (he ▸ ha)
      omega
    let p' : Fin d := ⟨p.val,hp⟩
    have he : p'.castSucc=p := rfl
    refine ⟨p',he.symm ▸ ha,encode.injective ?_⟩
    apply Fin.ext
    change value (applyCarry p'.castSucc a)=value b
    rw [he,carry_value p a ha,ite_eq_right (Nat.ne_of_lt hp),hab]

theorem value_eq_zero_iff {d m : ℕ} (hm : 0< m) (a : Word d m) :
    value a=0 ↔ ∀ i,(a i).val=0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [value_succ,Fin.forall_fin_succ]
    constructor
    · intro h
      have hz : value (fun i : Fin d => a i.succ)=0 := by nlinarith
      exact ⟨by omega,(ih _).mp hz⟩
    · rintro ⟨h0,ht⟩
      rw [h0,(ih _).mpr ht]
      omega

theorem allowed_last_iff {d m : ℕ} (a : Word d m) :
    Allowed (Fin.last d) a ↔ ∀ i,(a i).val+1=m := by
  simp only [allowed_iff,Fin.val_last,Fin.isLt,ite_true]

theorem value_last_iff {d m : ℕ} (a : Word d m) :
    value a+1=m^d ↔ ∀ i,(a i).val+1=m := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := exists_allowed a
    have he : p.val=d := by
      by_contra hn
      have hb := (encode (applyCarry p a)).isLt
      change value (applyCarry p a)< m^d at hb
      rw [carry_value p a hp,ite_eq_right hn,h] at hb
      omega
    have he' : p=Fin.last d := Fin.ext he
    exact allowed_last_iff a |>.mp (he' ▸ hp)
  · intro h
    exact wrap_value a ((allowed_last_iff a).mpr h)

end WLTime.Digits

namespace WLTime.ProductBox
abbrev Address (r m : ℕ) := Fin r → Fin m

structure Box (r m : ℕ) where
  domain : Fin r → Finset (Fin m)
  coord : Fin r → Equiv.Perm (Fin m)

namespace Box
variable {r m : ℕ} (B : Box r m)

def Allowed (a : Address r m) : Prop := ∀ i, a i ∈ B.domain i

def apply (a : Address r m) : Address r m := fun i => B.coord i (a i)

def Rel (a b : Address r m) : Prop := B.Allowed a ∧ B.apply a=b

def reverse : Box r m where
  domain i := (B.domain i).image (B.coord i)
  coord i := (B.coord i).symm

@[simp] theorem reverse_apply_apply (a : Address r m) : B.reverse.apply (B.apply a)=a := by
  funext i
  exact (B.coord i).symm_apply_apply (a i)

@[simp] theorem apply_reverse_apply (a : Address r m) : B.apply (B.reverse.apply a)=a := by
  funext i
  exact (B.coord i).apply_symm_apply (a i)

theorem reverse_allowed (a : Address r m) : B.reverse.Allowed a ↔ B.Allowed (B.reverse.apply a) := by
  unfold Allowed reverse apply
  apply forall_congr'
  intro i
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    simpa only [← he,Equiv.symm_apply_apply] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨(B.coord i).symm (a i),h,(B.coord i).apply_symm_apply (a i)⟩

theorem reverse_relation (a b : Address r m) : B.reverse.Rel a b ↔ B.Rel b a := by
  rw [Rel,reverse_allowed,Rel]
  constructor
  · rintro ⟨ha,hab⟩
    exact ⟨hab ▸ ha,by rw [← hab,B.apply_reverse_apply]⟩
  · rintro ⟨hb,hba⟩
    rw [← hba,B.reverse_apply_apply]
    exact ⟨hb,rfl⟩

def identity (r m : ℕ) : Box r m where
  domain _ := Finset.univ
  coord _ := Equiv.refl _

@[simp] theorem identity_rel (a b : Address r m) : (identity r m).Rel a b ↔ a=b := by
  change ((∀ i, a i ∈ (Finset.univ : Finset (Fin m))) ∧ a=b) ↔ a=b
  simp

def product {d q : ℕ} (B : Box d m) (C : Box q m) : Box (d+q) m where
  domain := Fin.addCases B.domain C.domain
  coord := Fin.addCases B.coord C.coord

@[simp] theorem product_allowed {d q : ℕ} (B : Box d m) (C : Box q m)
    (a : Address d m) (b : Address q m) :
    (B.product C).Allowed (Fin.append a b) ↔ B.Allowed a ∧ C.Allowed b := by
  simp [Allowed,product,Fin.forall_fin_add]

@[simp] theorem product_apply {d q : ℕ} (B : Box d m) (C : Box q m)
    (a : Address d m) (b : Address q m) :
    (B.product C).apply (Fin.append a b)=Fin.append (B.apply a) (C.apply b) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [apply,product]

def carry {d m : ℕ} (p : Fin (d+1)) : Box d m where
  domain := Digits.CarryDomain p
  coord := Digits.coordinate p

theorem carry_rel {d m : ℕ} (a b : Address d m) :
    (∃ p : Fin (d+1), (carry p).Rel a b) ↔
      Digits.encode b=Digits.inc (m^d) (Digits.encode a) :=
  Digits.carry_relation a b

theorem borrow_rel {d m : ℕ} (a b : Address d m) :
    (∃ p : Fin (d+1), (carry p).reverse.Rel a b) ↔
      Digits.encode b=(Digits.inc (m^d)).symm (Digits.encode a) := by
  simp_rw [reverse_relation]
  rw [carry_rel]
  constructor
  · intro h
    have he := congrArg (Digits.inc (m^d)).symm h
    simpa only [Equiv.symm_apply_apply] using he.symm
  · intro h
    have he := congrArg (Digits.inc (m^d)) h
    simpa only [Equiv.apply_symm_apply] using he.symm

end Box
end WLTime.ProductBox

namespace WLTime.ProductBox
abbrev time {d q m : ℕ} (a : Address (d+q) m) : Address d m := fun i => a (i.castAdd q)
abbrev space {d q m : ℕ} (a : Address (d+q) m) : Address q m := fun i => a (i.natAdd d)

@[simp] theorem append_time_space {d q m : ℕ} (a : Address (d+q) m) :
    Fin.append (time a) (space a)=a := Fin.append_castAdd_natAdd

@[simp] theorem time_append {d q m : ℕ} (a : Address d m) (b : Address q m) :
    time (Fin.append a b)=a := by funext i; exact Fin.append_left _ _ _
@[simp] theorem space_append {d q m : ℕ} (a : Address d m) (b : Address q m) :
    space (Fin.append a b)=b := by funext i; exact Fin.append_right _ _ _

def addressEquiv {d q m : ℕ} : Address (d+q) m ≃ Fin (m^d) × Fin (m^q) where
  toFun a := (Digits.encode (time a),Digits.encode (space a))
  invFun b := Fin.append (Digits.encode.symm b.1) (Digits.encode.symm b.2)
  left_inv a := by simp
  right_inv b := by simp

namespace Box
variable {d q m : ℕ}
theorem product_relation (B : Box d m) (C : Box q m) (a b : Address (d+q) m) :
    (B.product C).Rel a b ↔ B.Rel (time a) (time b) ∧ C.Rel (space a) (space b) := by
  rw [← append_time_space a,← append_time_space b]
  simp only [Rel,product_allowed,product_apply,time_append,space_append]
  have he {a a' : Address d m} {b b' : Address q m} :
      Fin.append a b=Fin.append a' b' ↔ a=a' ∧ b=b' := by
    constructor
    · intro h
      exact ⟨by simpa using congrArg time h,by simpa using congrArg space h⟩
    · rintro ⟨rfl,rfl⟩; rfl
  rw [he]
  tauto
end Box
end WLTime.ProductBox

namespace WLTime.NatCode
namespace Expr
variable {J : Type uJ}
def choose (p : Predicate J) (a b : Expr J) : Expr J :=
  .binary .add (.binary .mul p.code a) (.binary .mul (.binary .sub (.const 1) p.code) b)

 theorem choose_eval (p : Predicate J) (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (choose p a b).eval σ w=if p.Holds σ w then a.eval σ w else b.eval σ w := by
  simp only [choose,eval,Binary.eval,Predicate.code_eval]
  split_ifs <;> simp

 theorem choose_bounded (p : Predicate J) (a b : Expr J) (σ : J → ℕ) (w : List Bool)
    (B : ℕ) (hp : p.Bounded σ w B) (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) :
    (choose p a b).Bounded σ w (2*B+1) := by
  have hp' := p.code_bounded σ w B hp
  have ha' := a.bounded_mono σ w ha (by omega : B≤2*B+1)
  have hb' := b.bounded_mono σ w hb (by omega : B≤2*B+1)
  have hva := a.eval_le σ w B ha
  have hvb := b.eval_le σ w B hb
  refine ⟨⟨hp',ha',?_⟩,⟨⟨by change 1≤2*B+1; omega,hp',?_⟩,hb',?_⟩,?_⟩
  · simp only [Binary.eval,Predicate.code_eval]; split_ifs <;> simp_all; omega
  · change 1-p.code.eval σ w≤2*B+1; omega
  · simp only [Binary.eval,eval,Predicate.code_eval]; split_ifs <;> simp_all; omega
  · change (choose p a b).eval σ w≤2*B+1
    rw [choose_eval]; split_ifs <;> omega

def incCode (M a : Expr J) : Expr J :=
  choose (.eq (.binary .add a (.const 1)) M) (.const 0) (.binary .add a (.const 1))
def decCode (M a : Expr J) : Expr J :=
  choose (.eq a (.const 0)) (.binary .sub M (.const 1)) (.binary .sub a (.const 1))

 theorem incCode_eval {m : ℕ} (x : Fin m) (M a : Expr J) (σ : J → ℕ) (w : List Bool)
    (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (incCode M a).eval σ w=(Digits.inc m x).val := by
  rw [incCode,choose_eval,Digits.inc_value]
  simp only [Predicate.Holds,eval,Binary.eval,hM,ha]

 theorem decCode_eval {m : ℕ} (x : Fin m) (M a : Expr J) (σ : J → ℕ) (w : List Bool)
    (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (decCode M a).eval σ w=((Digits.inc m).symm x).val := by
  have h := Digits.inc_value ((Digits.inc m).symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [decCode,choose_eval]
  simp only [Predicate.Holds,eval,Binary.eval,hM,ha]
  have hh := ((Digits.inc m).symm x).isLt
  split_ifs at h ⊢ <;> omega
end Expr
end WLTime.NatCode

namespace WLTime.ProductBox
open NatCode
namespace Formula
variable {d q m : ℕ} {J : Type uJ}

def carryDomain (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Predicate J :=
  if i.val<p.val then .eq (.binary .add a (.const 1)) M
  else if i.val=p.val then .lt (.binary .add a (.const 1)) M else .truth true

def carryCoord (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Expr J :=
  if i.val≤p.val then Expr.incCode M a else a

def borrowCoord (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Expr J :=
  if i.val≤p.val then Expr.decCode M a else a

def borrowDomain (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Predicate J :=
  carryDomain p i M (borrowCoord p i M a)

 theorem carryDomain_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (carryDomain p i M a).Holds σ w ↔ x∈(Box.carry p).domain i := by
  simp only [Box.carry,Digits.CarryDomain,Finset.mem_filter,Finset.mem_univ,true_and,carryDomain]
  split_ifs <;> simp only [Predicate.Holds,Expr.eval,Binary.eval,ha,hM]

 theorem carryCoord_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (carryCoord p i M a).eval σ w=((Box.carry p).coord i x).val := by
  simp only [carryCoord,Box.carry,Digits.coordinate]
  split_ifs
  · exact Expr.incCode_eval x M a σ w hM ha
  · exact ha

 theorem borrowCoord_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (borrowCoord p i M a).eval σ w=((Box.carry p).reverse.coord i x).val := by
  simp only [borrowCoord,Box.reverse,Box.carry,Digits.coordinate]
  split_ifs
  · exact Expr.decCode_eval x M a σ w hM ha
  · exact ha

 theorem borrowDomain_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (borrowDomain p i M a).Holds σ w ↔ x∈(Box.carry p).reverse.domain i := by
  rw [borrowDomain,carryDomain_correct p i M _ σ w _ hM (borrowCoord_correct p i M a σ w x hM ha)]
  change (Digits.coordinate p i).symm x∈(Box.carry p).domain i ↔ _
  simp only [Box.reverse,Finset.mem_image]
  constructor
  · intro h; exact ⟨(Digits.coordinate p i).symm x,h,Equiv.apply_symm_apply _ _⟩
  · rintro ⟨y,hy,he⟩
    change Digits.coordinate p i y=x at he
    rw [← he,Equiv.symm_apply_apply]
    exact hy
end Formula
end WLTime.ProductBox

end OAI
