import OAI.Computability.FiniteCompiler.Quotients

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine
/-- An unreduced dyadic numerator difference and a power-of-two denominator.
    Computation never relies on Mathlib's noncomputable coding of `ℚ`. -/
abbrev Dyad := ℕ × ℕ × ℕ
namespace Dyad
def val (a : Dyad) : ℚ := ((a.1:ℚ)-a.2.1)/2^a.2.2
def zero : Dyad := (0,0,0)
def one : Dyad := (1,0,0)
def neg (a : Dyad) : Dyad := (a.2.1,a.1,a.2.2)
def add (a b : Dyad) : Dyad :=
  (a.1*2^b.2.2+b.1*2^a.2.2,a.2.1*2^b.2.2+b.2.1*2^a.2.2,a.2.2+b.2.2)
def mul (a b : Dyad) : Dyad :=
  (a.1*b.1+a.2.1*b.2.1,a.1*b.2.1+a.2.1*b.1,a.2.2+b.2.2)
def le (a b : Dyad) : Bool :=
  decide (a.1*2^b.2.2+b.2.1*2^a.2.2 ≤ b.1*2^a.2.2+a.2.1*2^b.2.2)
def eq (a b : Dyad) : Bool := le a b && le b a
def max (a b : Dyad) : Dyad := if le a b then b else a

@[simp] theorem val_zero : val zero=0 := by norm_num [val,zero]
@[simp] theorem val_one : val one=1 := by norm_num [val,one]
@[simp] theorem val_neg (a : Dyad) : val (neg a) = -val a := by simp [val,neg]; ring
@[simp] theorem val_add (a b : Dyad) : val (add a b)=val a+val b := by
  simp only [val,add,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  field_simp
  ring
@[simp] theorem val_mul (a b : Dyad) : val (mul a b)=val a*val b := by
  simp only [val,mul,Nat.cast_add,Nat.cast_mul,pow_add]
  field_simp
  ring
@[simp] theorem le_correct (a b : Dyad) : le a b=true ↔ val a≤val b := by
  rw [val,val,div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [le,decide_eq_true_eq]
  rw [← Nat.cast_le (α:=ℚ)]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  constructor <;> intro h <;> nlinarith
@[simp] theorem eq_correct (a b : Dyad) : eq a b=true ↔ val a=val b := by
  rw [eq, Bool.and_eq_true, le_correct, le_correct]
  exact le_antisymm_iff.symm
@[simp] theorem val_max (a b : Dyad) : val (max a b)=Max.max (val a) (val b) := by
  unfold max
  split
  next h => exact (max_eq_right ((le_correct a b).mp h)).symm
  next h => exact (max_eq_left (le_of_not_ge fun hh => h ((le_correct a b).mpr hh))).symm

theorem primrec_pow2 : Primrec (fun n : ℕ => 2^n) :=
  (Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂).of_eq
    (by intro n; induction n <;> simp_all [pow_succ])

theorem primrec_neg : Primrec neg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

theorem primrec_add : Primrec₂ add := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap (primrec_pow2.comp bk))
    (Primrec.nat_mul.comp bp (primrec_pow2.comp ak))).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp an (primrec_pow2.comp bk))
      (Primrec.nat_mul.comp bn (primrec_pow2.comp ak))).pair
        (Primrec.nat_add.comp ak bk))).to₂

theorem primrec_mul : Primrec₂ mul := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bp) (Primrec.nat_mul.comp an bn)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bn) (Primrec.nat_mul.comp an bp)).pair
      (Primrec.nat_add.comp ak bk))).to₂

theorem primrec_le : Primrec₂ le := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_le.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp ap (primrec_pow2.comp bk))
      (Primrec.nat_mul.comp bn (primrec_pow2.comp ak)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp bp (primrec_pow2.comp ak))
      (Primrec.nat_mul.comp an (primrec_pow2.comp bk)))).decide).to₂

theorem primrec_eq : Primrec₂ eq :=
  (Primrec.and.comp (primrec_le.comp Primrec.fst Primrec.snd)
    (primrec_le.comp Primrec.snd Primrec.fst)).to₂

theorem primrec_max : Primrec₂ max :=
  (Primrec.ite (Primrec.eq.comp primrec_le (Primrec.const true)) Primrec.snd Primrec.fst).to₂

end Dyad

abbrev Slope := ℕ × ℕ
namespace Slope
def dyad (a : Slope) : Dyad := (2^a.1,0,a.2)
def val (a : Slope) : ℚ := Dyad.val (dyad a)
def mul (a b : Slope) : Slope := (a.1+b.1,a.2+b.2)
def inv (a : Slope) : Slope := (a.2,a.1)
@[simp] theorem val_eq (a : Slope) : val a=2^a.1/2^a.2 := by simp [val,dyad,Dyad.val]
theorem val_pos (a : Slope) : 0<val a := by rw [val_eq]; positivity
@[simp] theorem val_mul (a b : Slope) : val (mul a b)=val a*val b := by
  simp only [val_eq,mul,pow_add]
  ring
@[simp] theorem val_inv (a : Slope) : val (inv a)=(val a)⁻¹ := by simp [val_eq,inv]
theorem primrec_dyad : Primrec dyad :=
  (Dyad.primrec_pow2.comp Primrec.fst).pair ((Primrec.const 0).pair Primrec.snd)
theorem primrec_mul : Primrec₂ mul :=
  ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
theorem primrec_inv : Primrec inv := Primrec.snd.pair Primrec.fst
end Slope

namespace Bound
def dom : Option ℚ → ℚ → Prop
  | none,_ => True
  | some r,x => r≤x
instance (r : Option ℚ) (x : ℚ) : Decidable (dom r x) := by cases r <;> unfold dom <;> infer_instance

def sup : Option Dyad → Option Dyad → Option Dyad
  | none,b => b
  | a,none => a
  | some a,some b => some (Dyad.max a b)

theorem dom_sup (a b : Option Dyad) (x : ℚ) :
    dom ((sup a b).map Dyad.val) x ↔ dom (a.map Dyad.val) x ∧ dom (b.map Dyad.val) x := by
  cases a <;> cases b <;> simp [sup,dom,Dyad.val_max]

theorem dom_preimage (r : Option Dyad) (c : Slope) (d : Dyad) (x : ℚ) :
    dom ((r.map fun r => Dyad.mul (Slope.dyad (Slope.inv c)) (Dyad.add r (Dyad.neg d))).map Dyad.val) x ↔
      dom (r.map Dyad.val) (Slope.val c*x+Dyad.val d) := by
  cases r with
  | none => simp [dom]
  | some r =>
    simp only [Option.map_some,dom,Dyad.val_mul,Dyad.val_add,Dyad.val_neg]
    rw [show Dyad.val (Slope.dyad (Slope.inv c)) = (Slope.val c)⁻¹ from Slope.val_inv c,
      ← sub_eq_add_neg]
    rw [← div_eq_inv_mul,div_le_iff₀ (Slope.val_pos c)]
    constructor <;> intro h <;> linarith

theorem primrec_sup : Primrec₂ sup := by
  have hh : Primrec (fun p : Option Dyad × Option Dyad =>
      (Option.casesOn p.1 p.2 (fun a => Option.casesOn p.2 (some a) (fun b => some (Dyad.max a b))) : Option Dyad)) := by
    apply Primrec.option_casesOn Primrec.fst Primrec.snd
    exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.option_some.comp (Dyad.primrec_max.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂
  exact hh.of_eq (by intro p; rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl)
end Bound

abbrev Data := Slope × Dyad × Option Dyad
namespace Data
def mul (a b : Data) : Data :=
  (Slope.mul a.1 b.1, Dyad.add (Dyad.mul (Slope.dyad a.1) b.2.1) a.2.1,
    Bound.sup b.2.2 (a.2.2.map fun r =>
      Dyad.mul (Slope.dyad (Slope.inv b.1)) (Dyad.add r (Dyad.neg b.2.1))))
def one : Data := ((0,0),Dyad.zero,none)
def act (a : Data) (x : ℚ) : Option ℚ :=
  if Bound.dom (a.2.2.map Dyad.val) x then some (Slope.val a.1*x+Dyad.val a.2.1) else none

def represent (a : Data) : Function.End (Option ℚ) := fun o => o.bind (act a)

 theorem act_mul (a b : Data) (x : ℚ) : act (mul a b) x = (act b x).bind (act a) := by
  have hd : Bound.dom ((mul a b).2.2.map Dyad.val) x ↔
      Bound.dom (b.2.2.map Dyad.val) x ∧
      Bound.dom (a.2.2.map Dyad.val) (Slope.val b.1*x+Dyad.val b.2.1) := by
    rw [mul,Bound.dom_sup,Bound.dom_preimage]
  simp only [act,hd]
  split_ifs <;> simp_all only [Option.bind_some,Option.bind_none,act,↓reduceIte,
    and_true,true_and,false_and,not_false_eq_true]
  change some (Slope.val (Slope.mul a.1 b.1)*x+
    Dyad.val (Dyad.add (Dyad.mul (Slope.dyad a.1) b.2.1) a.2.1)) = _
  rw [Slope.val_mul,Dyad.val_add,Dyad.val_mul]
  change some (Slope.val a.1*Slope.val b.1*x+(Slope.val a.1*Dyad.val b.2.1+Dyad.val a.2.1)) = _
  congr 1
  ring

 theorem represent_mul (a b : Data) : represent (mul a b)=represent a*represent b := by
  funext o
  cases o with
  | none => rfl
  | some x => exact act_mul a b x

 theorem represent_one : represent one=1 := by
  funext o
  change represent one o = o
  cases o <;> simp [represent,act,one,Bound.dom,Slope.val_eq,Dyad.val_zero]

/-- The three literal parameters determine exactly a partial affine map. -/
def params (a : Data) : ℚ × ℚ × Option ℚ :=
  (Slope.val a.1,Dyad.val a.2.1,a.2.2.map Dyad.val)

 theorem represent_of_params {a b : Data} (h : params a=params b) : represent a=represent b := by
  have hs := congrArg Prod.fst h
  have ht := congrArg (fun p : ℚ × ℚ × Option ℚ => p.2.1) h
  have hd := congrArg (fun p : ℚ × ℚ × Option ℚ => p.2.2) h
  funext o
  cases o <;> simp_all [params,represent,act]

theorem domain_eq {a b : Data} (h : represent a=represent b) (x : ℚ) :
    Bound.dom (a.2.2.map Dyad.val) x ↔ Bound.dom (b.2.2.map Dyad.val) x := by
  have hh := congrFun h (some x)
  simp only [represent,Option.bind_some,act] at hh
  split_ifs at hh <;> simp_all

 theorem params_of_represent {a b : Data} (h : represent a=represent b) : params a=params b := by
  have hd : a.2.2.map Dyad.val=b.2.2.map Dyad.val := by
    cases ha : a.2.2.map Dyad.val with
    | none =>
      cases hb : b.2.2.map Dyad.val with
      | none => rfl
      | some s =>
        have hh := (domain_eq h (s-1)).mp (by simp [ha,Bound.dom])
        simp only [hb,Bound.dom] at hh
        linarith
    | some r =>
      cases hb : b.2.2.map Dyad.val with
      | none =>
        have hh := (domain_eq h (r-1)).mpr (by simp [hb,Bound.dom])
        simp only [ha,Bound.dom] at hh
        linarith
      | some s =>
        apply congrArg some
        apply le_antisymm
        · have hh := (domain_eq h s).mpr (by simp [hb,Bound.dom])
          simpa only [ha,Bound.dom] using hh
        · have hh := (domain_eq h r).mp (by simp [ha,Bound.dom])
          simpa only [hb,Bound.dom] using hh
  let x : ℚ := (a.2.2.map Dyad.val).getD 0
  have hx : Bound.dom (a.2.2.map Dyad.val) x := by
    cases ha : a.2.2.map Dyad.val <;> simp [x,ha,Bound.dom]
  have hx' : Bound.dom (a.2.2.map Dyad.val) (x+1) := by
    cases ha : a.2.2.map Dyad.val <;> simp [x,ha,Bound.dom]
  have hv (y : ℚ) (hy : Bound.dom (a.2.2.map Dyad.val) y) :
      Slope.val a.1*y+Dyad.val a.2.1=Slope.val b.1*y+Dyad.val b.2.1 := by
    have hh := congrFun h (some y)
    simp only [represent,Option.bind_some,act,ite_eq_left hy,ite_eq_left ((domain_eq h y).mp hy),Option.some.injEq] at hh
    exact hh
  have h0 := hv x hx
  have h1 := hv (x+1) hx'
  have hs : Slope.val a.1=Slope.val b.1 := by nlinarith
  have ht : Dyad.val a.2.1=Dyad.val b.2.1 := by rw [hs] at h0; linarith
  exact Prod.ext hs (Prod.ext ht hd)

 theorem represent_eq_iff (a b : Data) : represent a=represent b ↔ params a=params b :=
  ⟨params_of_represent,represent_of_params⟩

end Data

namespace Bound
def eq : Option Dyad → Option Dyad → Bool
  | none,none => true
  | some a,some b => Dyad.eq a b
  | _,_ => false

 theorem eq_correct (a b : Option Dyad) : eq a b=true ↔ a.map Dyad.val=b.map Dyad.val := by
  cases a <;> cases b <;> simp [eq,Dyad.eq_correct]

 theorem primrec_eq : Primrec₂ eq := by
  have hh : Primrec (fun p : Option Dyad × Option Dyad =>
      (Option.casesOn p.1 (Option.casesOn p.2 true (fun _ => false))
        (fun a => Option.casesOn p.2 false (fun b => Dyad.eq a b)) : Bool)) := by
    apply Primrec.option_casesOn Primrec.fst
    · exact Primrec.option_casesOn Primrec.snd (Primrec.const true) (Primrec.const false).to₂
    · exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst) (Primrec.const false)
        (Dyad.primrec_eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact hh.of_eq (by intro p; rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl)

 theorem primrec_preimage {X : Type*} [Primcodable X]
    {r : X → Option Dyad} {c : X → Slope} {d : X → Dyad}
    (hr : Primrec r) (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun x => (r x).map fun b =>
      Dyad.mul (Slope.dyad (Slope.inv (c x))) (Dyad.add b (Dyad.neg (d x)))) :=
  Primrec.option_map hr
    ((Dyad.primrec_mul.comp (Slope.primrec_dyad.comp (Slope.primrec_inv.comp (hc.comp Primrec.fst)))
      (Dyad.primrec_add.comp Primrec.snd (Dyad.primrec_neg.comp (hd.comp Primrec.fst)))).to₂)
end Bound

namespace Data
def eq (a b : Data) : Bool :=
  Dyad.eq (Slope.dyad a.1) (Slope.dyad b.1) &&
    Dyad.eq a.2.1 b.2.1 && Bound.eq a.2.2 b.2.2

 theorem eq_correct (a b : Data) : eq a b=true ↔ represent a=represent b := by
  rw [represent_eq_iff]
  simp only [eq,Bool.and_eq_true,Dyad.eq_correct,Bound.eq_correct,params,Prod.mk.injEq]
  change ((Slope.val a.1=Slope.val b.1) ∧ (Dyad.val a.2.1=Dyad.val b.2.1)) ∧ _ ↔ _
  exact and_assoc

 theorem primrec_mul : Primrec₂ mul := by
  have ac : Primrec (fun p : Data × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have ad : Primrec (fun p : Data × Data => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ar : Primrec (fun p : Data × Data => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bc : Primrec (fun p : Data × Data => p.2.1) := Primrec.fst.comp Primrec.snd
  have bd : Primrec (fun p : Data × Data => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have br : Primrec (fun p : Data × Data => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Slope.primrec_mul.comp ac bc).pair
    ((Dyad.primrec_add.comp (Dyad.primrec_mul.comp (Slope.primrec_dyad.comp ac) bd) ad).pair
      (Bound.primrec_sup.comp br (Bound.primrec_preimage ar bc bd)))).to₂

 theorem primrec_eq : Primrec₂ eq := by
  exact (Primrec.and.comp
    (Primrec.and.comp
      (Dyad.primrec_eq.comp (Slope.primrec_dyad.comp (Primrec.fst.comp Primrec.fst))
        (Slope.primrec_dyad.comp (Primrec.fst.comp Primrec.snd)))
      (Dyad.primrec_eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    (Bound.primrec_eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
end Data

/-- The fixed six-letter alphabet in the algebra construction, in the order
    `u,v,u⁻¹,v⁻¹,e₀,e₁`. -/
abbrev Letter := Fin 6

def generator (i : Letter) : Data :=
  if i=0 then ((0,1),Dyad.zero,none)
  else if i=1 then ((0,1),(1,0,1),none)
  else if i=2 then ((1,0),Dyad.zero,none)
  else if i=3 then ((1,0),(0,1,0),none)
  else if i=4 then ((0,0),Dyad.zero,some Dyad.zero)
  else ((0,0),Dyad.zero,some Dyad.one)

def evaluate (w : List Letter) : Data := w.foldr (fun i d => Data.mul (generator i) d) Data.one

def value (w : List Letter) : Function.End (Option ℚ) := (w.map (Data.represent ∘ generator)).prod

 theorem represent_evaluate (w : List Letter) : Data.represent (evaluate w)=value w := by
  induction w with
  | nil => exact Data.represent_one
  | cons i w ih =>
    simpa only [evaluate,List.foldr_cons,value,List.map_cons,List.prod_cons,Function.comp_apply]
      using (Data.represent_mul (generator i) (evaluate w)).trans (congrArg (Data.represent (generator i)*·) ih)

 theorem primrec_evaluate : Primrec evaluate :=
  Primrec.list_foldr Primrec.id (Primrec.const Data.one)
    (Data.primrec_mul.comp ((Primrec.dom_finite generator).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- Lemma partial-affine, algorithmic part: a primitive-recursive equality test
    for the actual partial maps, not classical decidability. -/
 theorem primrec_word_equivalence : PrimrecPred (fun p : List Letter × List Letter => value p.1=value p.2) := by
  have hh : PrimrecPred (fun p : List Letter × List Letter => Data.eq (evaluate p.1) (evaluate p.2)=true) :=
    Primrec.eq.comp (Data.primrec_eq.comp (primrec_evaluate.comp Primrec.fst)
      (primrec_evaluate.comp Primrec.snd)) (Primrec.const true)
  exact hh.of_eq fun p => by rw [Data.eq_correct,represent_evaluate,represent_evaluate]

/-- A computable, uniquely comparable coding of the tested class for the
    auxiliary monoid. No rational-number coding is used as an oracle. -/
noncomputable def testedClass : List Letter → List Letter :=
  Bootstrap.Canonical.least (r:=fun a b : Letter => a<b) wellFounded_lt value

 theorem computable_testedClass : Computable testedClass := by
  classical
  apply Bootstrap.Canonical.computable_least
  · exact Bootstrap.Search.primrec_shortlex ⟨inferInstance,Primrec.dom_finite _⟩
  · exact ⟨inferInstance,primrec_word_equivalence.decide.to_comp⟩

 theorem testedClass_eq_iff (u v : List Letter) : testedClass u=testedClass v ↔ value u=value v := by
  classical
  exact Bootstrap.Canonical.least_eq_iff _ _

/-- The manuscript's auxiliary monoid is generated by the six actual partial
    affine maps. `none` is an undefined value; composition is right first. -/
def monoid : Submonoid (Function.End (Option ℚ)) :=
  Submonoid.closure (Set.range (Data.represent ∘ generator))

 theorem value_mem (w : List Letter) : value w∈monoid := by
  apply Submonoid.list_prod_mem
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  exact Submonoid.subset_closure ⟨i,rfl⟩

 theorem exists_word {a : Function.End (Option ℚ)} (ha : a∈monoid) : ∃ w,value w=a := by
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    exact ⟨[i],by simp [value]⟩
  | one => exact ⟨[],rfl⟩
  | mul a b ha hb ia ib =>
    obtain ⟨u,rfl⟩ := ia
    obtain ⟨v,rfl⟩ := ib
    exact ⟨u++v,by simp [value]⟩

def wordValue (w : List Letter) : monoid := ⟨value w,value_mem w⟩

 theorem wordValue_surjective : Function.Surjective wordValue := by
  intro a
  obtain ⟨w,hw⟩ := exists_word a.property
  exact ⟨w,Subtype.ext hw⟩

instance : Monoid.FG monoid := by
  unfold monoid
  infer_instance

instance : Countable monoid := Function.Surjective.countable wordValue_surjective

 theorem primrec_wordValue_equivalence : PrimrecPred
    (fun p : List Letter × List Letter => wordValue p.1=wordValue p.2) :=
  primrec_word_equivalence.of_eq (fun _ => ⟨fun h => Subtype.ext h,
    fun h => congrArg Subtype.val h⟩)

/-- Every element has the exact nonempty-tail form stated in
    Lemma partial-affine, including a full domain as `none`. -/
 theorem representation (a : monoid) : ∃ (d : Data),Data.represent d=a := by
  obtain ⟨w,hw⟩ := exists_word a.property
  exact ⟨evaluate w,(represent_evaluate w).trans hw⟩

 theorem nonempty_domain (a : monoid) : ∃ x y : ℚ,(a:Function.End (Option ℚ)) (some x)=some y := by
  obtain ⟨d,hd⟩ := representation a
  let x : ℚ := (d.2.2.map Dyad.val).getD 0
  have hx : Bound.dom (d.2.2.map Dyad.val) x := by
    cases h : d.2.2.map Dyad.val <;> simp [x,h,Bound.dom]
  refine ⟨x,Slope.val d.1*x+Dyad.val d.2.1,?_⟩
  rw [←hd]
  simp [Data.represent,Data.act,hx]

 theorem slope_integer_power (a : Slope) : ∃ m : ℤ,Slope.val a=(2:ℚ)^m := by
  refine ⟨(a.1:ℤ)-a.2,?_⟩
  rw [zpow_sub₀ (by norm_num),zpow_natCast,zpow_natCast,Slope.val_eq]

 theorem dyadic_value (a : Dyad) : ∃ (m : ℤ) (k : ℕ),Dyad.val a=(m:ℚ)/2^k := by
  refine ⟨(a.1:ℤ)-a.2.1,a.2.2,?_⟩
  simp [Dyad.val]

 theorem strictMono_on_domain (a : monoid) {x y u v : ℚ}
    (hx : (a:Function.End (Option ℚ)) (some x)=some u)
    (hy : (a:Function.End (Option ℚ)) (some y)=some v) (hxy : x<y) : u<v := by
  obtain ⟨d,hd⟩ := representation a
  rw [←hd] at hx hy
  simp only [Data.represent,Option.bind_some,Data.act] at hx hy
  split_ifs at hx
  split_ifs at hy
  have hu := Option.some.inj hx
  have hv := Option.some.inj hy
  rw [←hu,←hv]
  have h := mul_lt_mul_of_pos_left hxy (Slope.val_pos d.1)
  linarith

/-- Partial identities on rational tails, in the ambient partial-map monoid. -/
def tail (r : ℚ) : Function.End (Option ℚ) :=
  fun o => o.bind (fun x => if r≤x then some x else none)

 theorem tail_mul (r s : ℚ) : tail r*tail s=tail (max r s) := by
  funext o
  cases o with
  | none => rfl
  | some x =>
    change ((if s≤x then some x else none).bind
      (fun y => if r≤y then some y else none)) = if max r s≤x then some x else none
    by_cases hr : r ≤ x <;> by_cases hs : s ≤ x <;> simp [hr,hs]

 theorem tail_injective : Function.Injective tail := by
  intro r s h
  have hr := congrFun h (some r)
  have hs := congrFun h (some s)
  simp only [tail,Option.bind_some,le_refl,↓reduceIte] at hr hs
  have hsr : s ≤ r := by by_contra hn; simp [hn] at hr
  have hrs : r ≤ s := by by_contra hn; simp [hn] at hs
  exact le_antisymm hrs hsr

 theorem tail_ne_one (r : ℚ) : tail r≠1 := by
  intro h
  have hh := congrFun h (some (r-1))
  change (if r≤r-1 then some (r-1) else none)=some (r-1) at hh
  have hn : ¬r≤r-1 := by linarith
  simp [hn] at hh

 theorem generator_tail0 : Data.represent (generator 4)=tail 0 := by
  funext o
  cases o <;> simp [Data.represent,Data.act,generator,tail,Bound.dom,Slope.val_eq,Dyad.val_zero]

 theorem generator_tail1 : Data.represent (generator 5)=tail 1 := by
  funext o
  cases o <;> simp [Data.represent,Data.act,generator,tail,Bound.dom,Slope.val_eq,Dyad.val_zero,Dyad.val_one]

 theorem generator_u (o : Option ℚ) : Data.represent (generator 0) o=o.map (fun x => x/2) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val_zero,
    div_eq_mul_inv,mul_comm]

 theorem generator_v (o : Option ℚ) : Data.represent (generator 1) o=o.map (fun x => (x+1)/2) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val]
  ring

 theorem generator_ui (o : Option ℚ) : Data.represent (generator 2) o=o.map (fun x => 2*x) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val_zero]

 theorem generator_vi (o : Option ℚ) : Data.represent (generator 3) o=o.map (fun x => 2*x-1) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val]
  ring

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
