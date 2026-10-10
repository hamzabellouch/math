import OAI.NumberTheory.SingleFold.PolynomialCompiler

namespace OAI

namespace SingleFold

@[ext] structure RationalCode where
  p : ℕ
  n : ℕ
  d : ℕ
  t : ℕ
  s : ℕ
  q : ℕ
  deriving DecidableEq

namespace RationalCode

def Valid (z : RationalCode) : Prop :=
  z.p * z.n = 0 ∧ z.d = 1 + z.t + z.s ∧
  (z.p + z.n) * z.t + z.d = 1 + z.q * z.d

def value (z : RationalCode) : ℚ := ((z.p : ℚ) - z.n) / z.d

lemma den_pos {z : RationalCode} (h : z.Valid) : 0 < z.d := by
  have := h.2.1
  omega

lemma inverse_lt {z : RationalCode} (h : z.Valid) : z.t < z.d := by
  have := h.2.1
  omega

lemma inverse_mod {z : RationalCode} (h : z.Valid) :
    (z.p + z.n) * z.t ≡ 1 [MOD z.d] := by
  change ((z.p + z.n) * z.t) % z.d = 1 % z.d
  have hm := congrArg (fun a : ℕ => a % z.d) h.2.2
  simpa [Nat.add_mod, Nat.mul_mod] using hm

lemma reduced {z : RationalCode} (h : z.Valid) : (z.p + z.n).Coprime z.d :=
  Nat.coprime_of_mul_modEq_one z.t (inverse_mod h)

lemma abs_num {z : RationalCode} (h : z.Valid) :
    ((z.p : ℤ) - z.n).natAbs = z.p + z.n := by
  rcases Nat.mul_eq_zero.mp h.1 with hp | hn
  · simp [hp]
  · simp [hn]

lemma canonical {z : RationalCode} (h : z.Valid) :
    z.value.num = (z.p : ℤ) - z.n ∧ z.value.den = z.d := by
  have hr : ((z.p : ℤ) - z.n).natAbs.Coprime z.d := by
    rw [abs_num h]
    exact reduced h
  let r := Rat.mk' ((z.p : ℤ) - z.n) z.d (den_pos h).ne' hr
  have hv : z.value = r := by
    simpa only [r, Rat.mk', value, Int.cast_sub, Int.cast_natCast] using Rat.num_div_den r
  rw [hv]
  exact ⟨rfl, rfl⟩

lemma positive_num {z : RationalCode} (h : z.Valid) : z.value.num.toNat = z.p := by
  rw [(canonical h).1]
  rcases Nat.mul_eq_zero.mp h.1 with hp | hn
  · simp [hp]
  · simp [hn]

lemma negative_num {z : RationalCode} (h : z.Valid) : (-z.value.num).toNat = z.n := by
  rw [(canonical h).1]
  rcases Nat.mul_eq_zero.mp h.1 with hp | hn
  · simp [hp]
  · simp [hn]

theorem unique {z z' : RationalCode} (h : z.Valid) (h' : z'.Valid)
    (heq : z.value = z'.value) : z = z' := by
  have hp : z.p = z'.p := by rw [← positive_num h, ← positive_num h', heq]
  have hn : z.n = z'.n := by rw [← negative_num h, ← negative_num h', heq]
  have hd : z.d = z'.d := by rw [← (canonical h).2, ← (canonical h').2, heq]
  have hm : (z.p + z.n) * z.t ≡ (z.p + z.n) * z'.t [MOD z.d] := by
    have hi' := inverse_mod h'
    rw [← hp, ← hn, ← hd] at hi'
    exact (inverse_mod h).trans hi'.symm
  have ht : z.t = z'.t := by
    apply (hm.cancel_left_of_coprime (reduced h).symm).eq_of_lt_of_lt (inverse_lt h)
    rw [hd]
    exact inverse_lt h'
  have hs : z.s = z'.s := by
    have hd₁ := h.2.1
    have hd₂ := h'.2.1
    omega
  have hq : z.q = z'.q := by
    have he₁ := h.2.2
    have he₂ := h'.2.2
    rw [← hp, ← hn, ← hd, ← ht] at he₂
    have hx : z.q * z.d = z'.q * z.d := by omega
    exact Nat.eq_of_mul_eq_mul_right (den_pos h) hx
  exact RationalCode.ext hp hn hd ht hs hq

lemma inverse_exists {a d : ℕ} (hd : 0 < d) (hcop : a.Coprime d) :
    ∃ t s q : ℕ, d = 1 + t + s ∧ a * t + d = 1 + q * d := by
  by_cases hd1 : d = 1
  · subst d
    exact ⟨0, 0, 0, by omega, by simp⟩
  · obtain ⟨t, ht, hinv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
    refine ⟨t, d - 1 - t, (a * t) / d + 1, by omega, ?_⟩
    have hdiv := Nat.mod_add_div (a * t) d
    rw [hinv] at hdiv
    nlinarith

theorem existsUnique (r : ℚ) : ∃! z : RationalCode, z.Valid ∧ z.value = r := by
  let p := r.num.toNat
  let n := (-r.num).toNat
  have hpn : p * n = 0 := by
    rcases le_total 0 r.num with hn | hn
    · have : n = 0 := Int.toNat_eq_zero.mpr (neg_nonpos.mpr hn)
      simp [this]
    · have : p = 0 := Int.toNat_eq_zero.mpr hn
      simp [this]
  have habs : p + n = r.num.natAbs := Int.toNat_add_toNat_neg_eq_natAbs _
  obtain ⟨t, s, q, hd, hi⟩ := inverse_exists r.den_pos (habs ▸ r.reduced)
  let z : RationalCode := ⟨p, n, r.den, t, s, q⟩
  have hz : z.Valid := ⟨hpn, hd, hi⟩
  have hv : z.value = r := by
    have hn := Int.toNat_sub_toNat_neg r.num
    have hn' : (p : ℚ) - n = (r.num : ℚ) := by exact_mod_cast hn
    dsimp [value, z]
    rw [hn']
    exact r.num_div_den
  refine ⟨z, ⟨hz, hv⟩, ?_⟩
  intro z' hz'
  exact unique hz'.1 hz (hz'.2.trans hv.symm)

end RationalCode
end SingleFold

namespace SingleFold.Compiler.SF
variable {α β : Type} {R S : (α → ℕ) → Prop}

theorem congr (h : SF R) (he : ∀ x, R x ↔ S x) : SF S := by
  obtain ⟨r⟩ := h
  exact ⟨r.congr he⟩
theorem and (hR : SF R) (hS : SF S) : SF (fun x => R x ∧ S x) := by
  obtain ⟨r⟩ := hR; obtain ⟨s⟩ := hS
  exact ⟨r.and s⟩
theorem or (hR : SF R) (hS : SF S) (hd : ∀ x, ¬(R x ∧ S x)) : SF (fun x => R x ∨ S x) := by
  obtain ⟨r⟩ := hR; obtain ⟨s⟩ := hS
  exact ⟨r.or s hd⟩
theorem reindex (hR : SF R) (f : α → β) : SF (fun x => R (x ∘ f)) := by
  obtain ⟨r⟩ := hR; exact ⟨r.reindex f⟩
theorem all [Finite β] {R : β → (α → ℕ) → Prop} (hr : ∀ i, SF (R i)) : SF (fun x => ∀ i, R i x) :=
  ⟨Representation.all R (fun i => Classical.choice (hr i))⟩
theorem eq (p q : Poly α) : SF (fun x => p x=q x) := ⟨Representation.eq p q⟩
theorem le (p q : Poly α) : SF (fun x => p x≤q x) := ⟨Representation.le p q⟩
theorem lt (p q : Poly α) : SF (fun x => p x<q x) := ⟨Representation.lt p q⟩
theorem ex {R : (α ⊕ β → ℕ) → Prop} [Finite β] (hr : SF R)
    (hu : ∀ x y y', R (Sum.elim x y) → R (Sum.elim x y') → y=y') :
    SF (fun x => ∃ y, R (Sum.elim x y)) := by
  obtain ⟨r⟩ := hr; exact ⟨r.ex hu⟩
end SingleFold.Compiler.SF

namespace SingleFold.RationalCompiler
open Compiler

structure FractionPoly (α : Type) where
  num : Poly α
  den : Poly α

namespace FractionPoly
variable {α : Type}
def value (p : FractionPoly α) (z : α → ℕ) : ℚ := (p.num z : ℚ)/(p.den z : ℚ)
def const (r : ℚ) : FractionPoly α := ⟨Poly.const r.num,Poly.const r.den⟩
def add (p q : FractionPoly α) : FractionPoly α := ⟨p.num*q.den+q.num*p.den,p.den*q.den⟩
def mul (p q : FractionPoly α) : FractionPoly α := ⟨p.num*q.num,p.den*q.den⟩
def neg (p : FractionPoly α) : FractionPoly α := ⟨-p.num,p.den⟩

lemma const_value (r : ℚ) (z : α → ℕ) : (const r).value z=r := by
  simpa only [value,const,Poly.const_apply,Int.cast_natCast] using r.num_div_den
lemma add_value (p q : FractionPoly α) (z : α → ℕ) (hp : 0<p.den z) (hq : 0<q.den z) :
    (p.add q).value z=p.value z+q.value z := by
  have hp' : (p.den z:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q.den z:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [value,add,Poly.add_apply,Poly.mul_apply,Int.cast_add,Int.cast_mul]
  simpa only [mul_comm] using (div_add_div (p.num z : ℚ) (q.num z : ℚ) hp' hq').symm
lemma mul_value (p q : FractionPoly α) (z : α → ℕ) :
    (p.mul q).value z=p.value z*q.value z := by
  simp only [value,mul,Poly.mul_apply,Int.cast_mul,div_mul_div_comm]
lemma neg_value (p : FractionPoly α) (z : α → ℕ) : (p.neg).value z= -p.value z := by
  simp only [value,neg,Poly.neg_apply,Int.cast_neg,neg_div]

lemma eq_iff (p q : FractionPoly α) (z : α → ℕ) (hp : 0<p.den z) (hq : 0<q.den z) :
    p.value z=q.value z ↔ (p.num*q.den) z=(q.num*p.den) z := by
  have hp' : (p.den z:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q.den z:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [value,value,div_eq_div_iff hp' hq']
  simp only [Poly.mul_apply]
  exact_mod_cast (Iff.rfl : (p.num z:ℚ)*q.den z=q.num z*p.den z ↔ (p.num z:ℚ)*q.den z=q.num z*p.den z)

lemma le_iff (p q : FractionPoly α) (z : α → ℕ) (hp : 0<p.den z) (hq : 0<q.den z) :
    p.value z≤q.value z ↔ (p.num*q.den) z≤(q.num*p.den) z := by
  have hp' : (0:ℚ)<p.den z := by exact_mod_cast hp
  have hq' : (0:ℚ)<q.den z := by exact_mod_cast hq
  rw [value,value,div_le_div_iff₀ hp' hq']
  simp only [Poly.mul_apply]
  exact_mod_cast (Iff.rfl : (p.num z:ℚ)*q.den z≤q.num z*p.den z ↔ (p.num z:ℚ)*q.den z≤q.num z*p.den z)

lemma guarded_eq {D : (α → ℕ) → Prop} (hD : SF D) (p q : FractionPoly α)
    (hp : ∀ z, D z → 0<p.den z) (hq : ∀ z, D z → 0<q.den z) :
    SF (fun z => D z ∧ p.value z=q.value z) :=
  (hD.and (SF.eq (p.num*q.den) (q.num*p.den))).congr (fun z => by
    constructor
    · rintro ⟨hd,he⟩; exact ⟨hd,(p.eq_iff q z (hp z hd) (hq z hd)).mpr he⟩
    · rintro ⟨hd,he⟩; exact ⟨hd,(p.eq_iff q z (hp z hd) (hq z hd)).mp he⟩)
lemma guarded_le {D : (α → ℕ) → Prop} (hD : SF D) (p q : FractionPoly α)
    (hp : ∀ z, D z → 0<p.den z) (hq : ∀ z, D z → 0<q.den z) :
    SF (fun z => D z ∧ p.value z≤q.value z) :=
  (hD.and (SF.le (p.num*q.den) (q.num*p.den))).congr (fun z => by
    constructor
    · rintro ⟨hd,he⟩; exact ⟨hd,(p.le_iff q z (hp z hd) (hq z hd)).mpr he⟩
    · rintro ⟨hd,he⟩; exact ⟨hd,(p.le_iff q z (hp z hd) (hq z hd)).mp he⟩)
end FractionPoly

def code (z : Fin 6 → ℕ) : RationalCode := ⟨z 0,z 1,z 2,z 3,z 4,z 5⟩
def tuple (z : RationalCode) : Fin 6 → ℕ := ![z.p,z.n,z.d,z.t,z.s,z.q]
@[simp] lemma code_tuple (z : RationalCode) : code (tuple z)=z := by cases z; rfl
@[simp] lemma tuple_code (z : Fin 6 → ℕ) : tuple (code z)=z := by funext i; fin_cases i <;> rfl

def Valid {α : Type} (z : α × Fin 6 → ℕ) : Prop := ∀ i, (code (fun j => z (i,j))).Valid
def value {α : Type} (z : α × Fin 6 → ℕ) (i : α) : ℚ := (code (fun j => z (i,j))).value

def input {α : Type} (i : α) : FractionPoly (α × Fin 6) :=
  ⟨Poly.proj (i,0)-Poly.proj (i,1),Poly.proj (i,2)⟩
lemma input_value {α : Type} (i : α) (z : α × Fin 6 → ℕ) : (input i).value z=value z i := by
  simp only [FractionPoly.value,input,Poly.sub_apply,Poly.proj_apply,Int.cast_sub,
    Int.cast_natCast,value,RationalCode.value,code]
lemma input_pos {α : Type} (i : α) (z : α × Fin 6 → ℕ) (hz : Valid z) : 0<(input i).den z := by
  change (0:ℤ) < (z (i,2):ℤ)
  have h := RationalCode.den_pos (hz i)
  change 0 < z (i,2) at h
  exact_mod_cast h

lemma valid_single_fold {α : Type} [Finite α] : SF (@Valid α) := by
  apply SF.all
  intro i
  let p : Poly (α × Fin 6) := Poly.proj (i,0)
  let n : Poly (α × Fin 6) := Poly.proj (i,1)
  let d : Poly (α × Fin 6) := Poly.proj (i,2)
  let t : Poly (α × Fin 6) := Poly.proj (i,3)
  let s : Poly (α × Fin 6) := Poly.proj (i,4)
  let q : Poly (α × Fin 6) := Poly.proj (i,5)
  refine ((SF.eq (p*n) 0).and ((SF.eq d (1+t+s)).and (SF.eq ((p+n)*t+d) (1+q*d)))).congr ?_
  intro z
  simp only [p,n,d,t,s,q,Poly.proj_apply,Poly.mul_apply,Poly.add_apply,Poly.zero_apply,Poly.one_apply,code,RationalCode.Valid]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂,by exact_mod_cast h₃⟩
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂,by exact_mod_cast h₃⟩

inductive Expr (α : Type)
  | var (i : α)
  | const (q : ℚ)
  | add (p q : Expr α)
  | mul (p q : Expr α)
  | neg (p : Expr α)
namespace Expr
variable {α : Type}
def eval (x : α → ℚ) : Expr α → ℚ
  | var i => x i
  | const q => q
  | add p q => eval x p+eval x q
  | mul p q => eval x p*eval x q
  | neg p => -eval x p
def compile : Expr α → FractionPoly (α × Fin 6)
  | var i => input i
  | const q => FractionPoly.const q
  | add p q => (compile p).add (compile q)
  | mul p q => (compile p).mul (compile q)
  | neg p => (compile p).neg
lemma compile_spec (p : Expr α) (z : α × Fin 6 → ℕ) (hz : Valid z) :
    0<p.compile.den z ∧ p.compile.value z=p.eval (value z) := by
  induction p with
  | var i => exact ⟨input_pos i z hz,input_value i z⟩
  | const q => exact ⟨by change (0:ℤ)<(q.den:ℤ); exact_mod_cast q.den_pos,FractionPoly.const_value q z⟩
  | add p q hp hq =>
    exact ⟨mul_pos hp.1 hq.1,by simpa only [compile,eval,hp.2,hq.2] using FractionPoly.add_value p.compile q.compile z hp.1 hq.1⟩
  | mul p q hp hq =>
    exact ⟨mul_pos hp.1 hq.1,by simpa only [compile,eval,hp.2,hq.2] using FractionPoly.mul_value p.compile q.compile z⟩
  | neg p hp => exact ⟨hp.1,by simpa only [compile,eval,hp.2] using FractionPoly.neg_value p.compile z⟩

lemma eq_single_fold [Finite α] (p q : Expr α) :
    SF (fun z => Valid z ∧ p.eval (value z)=q.eval (value z)) := by
  have hp (z) (hz : Valid z) := (p.compile_spec z hz).1
  have hq (z) (hz : Valid z) := (q.compile_spec z hz).1
  refine (FractionPoly.guarded_eq valid_single_fold p.compile q.compile hp hq).congr ?_
  intro z
  exact and_congr_right (fun hz => by rw [(p.compile_spec z hz).2,(q.compile_spec z hz).2])
lemma le_single_fold [Finite α] (p q : Expr α) :
    SF (fun z => Valid z ∧ p.eval (value z)≤q.eval (value z)) := by
  have hp (z) (hz : Valid z) := (p.compile_spec z hz).1
  have hq (z) (hz : Valid z) := (q.compile_spec z hz).1
  refine (FractionPoly.guarded_le valid_single_fold p.compile q.compile hp hq).congr ?_
  intro z
  exact and_congr_right (fun hz => by rw [(p.compile_spec z hz).2,(q.compile_spec z hz).2])
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.Compiler

def Semi {α : Type} (R : (α → ℕ) → Prop) : Prop := SF R ∧ SF (fun x => ¬R x)
namespace Semi
variable {α β : Type} {R S : (α → ℕ) → Prop}
theorem congr (h : Semi R) (he : ∀ x, R x ↔ S x) : Semi S :=
  ⟨h.1.congr he,h.2.congr (fun x => not_congr (he x))⟩
theorem not (h : Semi R) : Semi (fun x => ¬R x) :=
  ⟨h.2,h.1.congr (fun _ => (not_not).symm)⟩
theorem and (hR : Semi R) (hS : Semi S) : Semi (fun x => R x ∧ S x) := by
  refine ⟨hR.1.and hS.1,?_⟩
  refine (hR.2.or (hR.1.and hS.2) (by intro x h; exact h.1 h.2.1)).congr ?_
  intro x; tauto
theorem or (hR : Semi R) (hS : Semi S) : Semi (fun x => R x ∨ S x) :=
  ((hR.not.and hS.not).not).congr (by intro x; tauto)
theorem reindex (hR : Semi R) (f : α → β) : Semi (fun x => R (x ∘ f)) :=
  ⟨hR.1.reindex f,hR.2.reindex f⟩
theorem eq (p q : Poly α) : Semi (fun x => p x=q x) := by
  refine ⟨SF.eq p q,((SF.lt p q).or (SF.lt q p) (by intro x h; exact lt_asymm h.1 h.2)).congr ?_⟩
  intro x; constructor
  · intro h; rcases h with h|h; exact h.ne; exact h.ne'
  · exact lt_or_gt_of_ne
theorem le (p q : Poly α) : Semi (fun x => p x≤q x) :=
  ⟨SF.le p q,(SF.lt q p).congr (fun _ => not_le.symm)⟩
theorem lt (p q : Poly α) : Semi (fun x => p x<q x) :=
  ⟨SF.lt p q,(SF.le q p).congr (fun _ => not_lt.symm)⟩
theorem all [Finite β] {P : β → (α → ℕ) → Prop} (hp : ∀ i, Semi (P i)) :
    Semi (fun x => ∀ i, P i x) := by
  classical
  let := Fintype.ofFinite β
  suffices ∀ s : Finset β, Semi (fun x => ∀ i∈s, P i x) by
    exact (this Finset.univ).congr (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty => exact (Semi.eq (0:Poly α) 0).congr (by simp)
  | @insert i s hi hs => exact ((hp i).and hs).congr (by simp)
end Semi
end SingleFold.Compiler

namespace SingleFold.RationalCompiler
open Compiler

lemma valid_semi {α : Type} [Finite α] : Semi (@Valid α) := by
  apply Semi.all
  intro i
  let p : Poly (α × Fin 6) := Poly.proj (i,0)
  let n : Poly (α × Fin 6) := Poly.proj (i,1)
  let d : Poly (α × Fin 6) := Poly.proj (i,2)
  let t : Poly (α × Fin 6) := Poly.proj (i,3)
  let s : Poly (α × Fin 6) := Poly.proj (i,4)
  let q : Poly (α × Fin 6) := Poly.proj (i,5)
  refine ((Semi.eq (p*n) 0).and ((Semi.eq d (1+t+s)).and (Semi.eq ((p+n)*t+d) (1+q*d)))).congr ?_
  intro z
  simp only [p,n,d,t,s,q,Poly.proj_apply,Poly.mul_apply,Poly.add_apply,Poly.zero_apply,Poly.one_apply,code,RationalCode.Valid]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂,by exact_mod_cast h₃⟩
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂,by exact_mod_cast h₃⟩
namespace Expr
variable {α β : Type}
instance : Add (Expr α) := ⟨Expr.add⟩
instance : Mul (Expr α) := ⟨Expr.mul⟩
instance : Neg (Expr α) := ⟨Expr.neg⟩
instance : Sub (Expr α) := ⟨fun p q => p+ -q⟩
instance (n : ℕ) : OfNat (Expr α) n := ⟨const n⟩
instance : Pow (Expr α) ℕ := ⟨fun p n => Nat.rec (1:Expr α) (fun _ q => p*q) n⟩
@[simp] lemma eval_add (p q : Expr α) (x) : (p+q).eval x=p.eval x+q.eval x := rfl
@[simp] lemma eval_mul (p q : Expr α) (x) : (p*q).eval x=p.eval x*q.eval x := rfl
@[simp] lemma eval_neg (p : Expr α) (x) : (-p).eval x= -p.eval x := rfl
@[simp] lemma eval_sub (p q : Expr α) (x) : (p-q).eval x=p.eval x-q.eval x := by change p.eval x+ -q.eval x=_; rw [sub_eq_add_neg]
@[simp] lemma eval_nat (n : ℕ) (x : α → ℚ) : (const n).eval x=n := rfl
@[simp] lemma eval_ofNat (n : ℕ) [n.AtLeastTwo] (x : α → ℚ) : (OfNat.ofNat n : Expr α).eval x=n := rfl
@[simp] lemma eval_zero (x : α → ℚ) : (0:Expr α).eval x=0 := rfl
@[simp] lemma eval_one (x : α → ℚ) : (1:Expr α).eval x=1 := rfl
@[simp] lemma eval_var (i : α) (x) : (var i).eval x=x i := rfl
@[simp] lemma eval_pow (p : Expr α) (n : ℕ) (x) : (p^n).eval x=(p.eval x)^n := by
  induction n with
  | zero => change (1:ℚ)=_; simp
  | succ n ih => change (p*(p^n)).eval x=_; rw [eval_mul,ih,pow_succ']

lemma eq_under {G : (β → ℕ) → Prop} (hG : Semi G) (f : α×Fin 6 → β)
    (hv : ∀ z, G z → Valid (z ∘ f)) (p q : Expr α) :
    Semi (fun z => G z ∧ p.eval (value (z ∘ f))=q.eval (value (z ∘ f))) := by
  refine (hG.and (Semi.eq ((p.compile.num*q.compile.den).map f) ((q.compile.num*p.compile.den).map f))).congr ?_
  intro z
  apply and_congr_right
  intro hz
  have hp := p.compile_spec (z ∘ f) (hv z hz)
  have hq := q.compile_spec (z ∘ f) (hv z hz)
  change (p.compile.num*q.compile.den) (z ∘ f)=(q.compile.num*p.compile.den) (z ∘ f) ↔ _
  rw [←FractionPoly.eq_iff _ _ _ hp.1 hq.1,hp.2,hq.2]
lemma le_under {G : (β → ℕ) → Prop} (hG : Semi G) (f : α×Fin 6 → β)
    (hv : ∀ z, G z → Valid (z ∘ f)) (p q : Expr α) :
    Semi (fun z => G z ∧ p.eval (value (z ∘ f))≤q.eval (value (z ∘ f))) := by
  refine (hG.and (Semi.le ((p.compile.num*q.compile.den).map f) ((q.compile.num*p.compile.den).map f))).congr ?_
  intro z
  apply and_congr_right
  intro hz
  have hp := p.compile_spec (z ∘ f) (hv z hz)
  have hq := q.compile_spec (z ∘ f) (hv z hz)
  change (p.compile.num*q.compile.den) (z ∘ f)≤(q.compile.num*p.compile.den) (z ∘ f) ↔ _
  rw [←FractionPoly.le_iff _ _ _ hp.1 hq.1,hp.2,hq.2]
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.RationalCode
noncomputable def encode (q : ℚ) : RationalCode := Classical.choose (existsUnique q)
lemma encode_valid (q : ℚ) : (encode q).Valid := (Classical.choose_spec (existsUnique q)).1.1
lemma encode_value (q : ℚ) : (encode q).value=q := (Classical.choose_spec (existsUnique q)).1.2
lemma eq_encode {z : RationalCode} (hz : z.Valid) : z=encode z.value :=
  unique hz (encode_valid _) (encode_value _).symm
end SingleFold.RationalCode

end OAI
