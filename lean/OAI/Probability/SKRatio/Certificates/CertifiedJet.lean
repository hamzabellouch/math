import Mathlib
import OAI.Probability.SKRatio.Calculus.PlusSpin
import OAI.Probability.SKRatio.Certificates.CertifiedInterval

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

structure Jet where
  val : Box
  der : Box
  sec : Box
  deriving DecidableEq, Repr

namespace Jet
open Box

def rat (q : ℚ) : Jet := ⟨Box.rat q,Box.rat 0,Box.rat 0⟩
def var (B : Box) : Jet := ⟨B,Box.rat 1,Box.rat 0⟩
def add (A B : Jet) : Jet := ⟨Box.add A.val B.val,Box.add A.der B.der,Box.add A.sec B.sec⟩
def neg (A : Jet) : Jet := ⟨Box.neg A.val,Box.neg A.der,Box.neg A.sec⟩
def mul (A B : Jet) : Jet :=
  ⟨Box.mul A.val B.val,
   Box.add (Box.mul A.der B.val) (Box.mul A.val B.der),
   Box.add (Box.add (Box.mul A.sec B.val) (Box.mul (Box.rat 2) (Box.mul A.der B.der))) (Box.mul A.val B.sec)⟩
def sq (A : Jet) : Jet := ⟨Box.sq A.val,Box.mul (Box.rat 2) (Box.mul A.val A.der),
  Box.mul (Box.rat 2) (Box.add (Box.sq A.der) (Box.mul A.val A.sec))⟩
def inv (A : Jet) : Option Jet := do
  let B ← Box.inv A.val
  return ⟨B,Box.neg (Box.mul A.der (Box.sq B)),
    Box.sub (Box.mul (Box.rat 2) (Box.mul (Box.sq A.der) (Box.mul B (Box.sq B)))) (Box.mul A.sec (Box.sq B))⟩
def exp (A : Jet) : Option Jet := do
  let B ← Box.exp A.val
  return ⟨B,Box.mul B A.der,Box.mul B (Box.add A.sec (Box.sq A.der))⟩

def tanhBox (A : Box) : Option Box := do
  let E ← Box.exp (Box.mul (Box.rat 2) A)
  let D ← Box.inv (Box.add E (Box.rat 1))
  return Box.mul (Box.sub E (Box.rat 1)) D

def tanh (A : Jet) : Option Jet := do
  let B ← tanhBox A.val
  let V := Box.sub (Box.rat 1) (Box.sq B)
  return ⟨B,Box.mul V A.der,Box.sub (Box.mul V A.sec)
    (Box.mul (Box.rat 2) (Box.mul B (Box.mul V (Box.sq A.der))))⟩

lemma tanh_formula (x : ℝ) : Real.tanh x = (Real.exp (2*x)-1)*(Real.exp (2*x)+1)⁻¹ := by
  have h := Calculus.exp_two_mul_one_sub_tanh x
  have hd : Real.exp (2*x)+1 ≠ 0 := by positivity
  apply (mul_right_cancel₀ hd)
  field_simp
  linarith only [h]

lemma mem_tanhBox {A B : Box} {x : ℝ} (hx : x ∈ A) (he : tanhBox A=some B) : Real.tanh x ∈ B := by
  simp only [tanhBox,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at he
  obtain ⟨E,hE,D,hD,rfl⟩ := he
  have he' := Box.mem_exp (Box.mem_mul (Box.mem_rat 2) hx) hE
  norm_num only [Rat.cast_ofNat] at he'
  have hd' := Box.mem_inv (Box.mem_add he' (Box.mem_rat 1)) hD
  rw [tanh_formula]
  exact Box.mem_mul (Box.mem_sub he' (by exact_mod_cast Box.mem_rat 1)) (by simpa only [Rat.cast_one] using hd'.1)
end Jet

inductive Expr where
  | rat : ℚ → Expr
  | var : Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | sq : Expr → Expr
  | inv : Expr → Expr
  | exp : Expr → Expr
  | tanh : Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

def val (e : Expr) (x : ℝ) : ℝ := match e with
  | rat q => q
  | var => x
  | add a b => a.val x+b.val x
  | neg a => -a.val x
  | mul a b => a.val x*b.val x
  | sq a => (a.val x)^2
  | inv a => (a.val x)⁻¹
  | exp a => Real.exp (a.val x)
  | tanh a => Real.tanh (a.val x)

def der (e : Expr) (x : ℝ) : ℝ := match e with
  | rat _ => 0
  | var => 1
  | add a b => a.der x+b.der x
  | neg a => -a.der x
  | mul a b => a.der x*b.val x+a.val x*b.der x
  | sq a => 2*a.val x*a.der x
  | inv a => -a.der x*((a.val x)⁻¹)^2
  | exp a => Real.exp (a.val x)*a.der x
  | tanh a => (1-(Real.tanh (a.val x))^2)*a.der x

def sec (e : Expr) (x : ℝ) : ℝ := match e with
  | rat _ => 0
  | var => 0
  | add a b => a.sec x+b.sec x
  | neg a => -a.sec x
  | mul a b => a.sec x*b.val x+2*a.der x*b.der x+a.val x*b.sec x
  | sq a => 2*(a.der x^2+a.val x*a.sec x)
  | inv a => 2*a.der x^2*((a.val x)⁻¹)^3-a.sec x*((a.val x)⁻¹)^2
  | exp a => Real.exp (a.val x)*(a.sec x+a.der x^2)
  | tanh a => (1-(Real.tanh (a.val x))^2)*a.sec x-
      2*Real.tanh (a.val x)*(1-(Real.tanh (a.val x))^2)*a.der x^2

def compute (e : Expr) (B : Box) : Option Jet := match e with
  | rat q => some (Jet.rat q)
  | var => some (Jet.var B)
  | add a b => do let A ← a.compute B; let C ← b.compute B; return Jet.add A C
  | neg a => do let A ← a.compute B; return Jet.neg A
  | mul a b => do let A ← a.compute B; let C ← b.compute B; return Jet.mul A C
  | sq a => do let A ← a.compute B; return Jet.sq A
  | inv a => do let A ← a.compute B; Jet.inv A
  | exp a => do let A ← a.compute B; Jet.exp A
  | tanh a => do let A ← a.compute B; Jet.tanh A

def Regular (e : Expr) (x : ℝ) : Prop := match e with
  | rat _ | var => True
  | add a b | mul a b => a.Regular x ∧ b.Regular x
  | neg a | sq a | exp a | tanh a => a.Regular x
  | inv a => a.Regular x ∧ a.val x ≠ 0

lemma derivatives (e : Expr) (x : ℝ) (h : e.Regular x) :
    HasDerivAt e.val (e.der x) x ∧ HasDerivAt e.der (e.sec x) x := by
  induction e with
  | rat q => exact ⟨hasDerivAt_const _ _,hasDerivAt_const _ _⟩
  | var => exact ⟨hasDerivAt_id _,hasDerivAt_const _ _⟩
  | add a b ha hb =>
    exact ⟨(ha h.1).1.add (hb h.2).1,(ha h.1).2.add (hb h.2).2⟩
  | neg a ha => exact ⟨(ha h).1.neg,(ha h).2.neg⟩
  | mul a b ha hb =>
    obtain ⟨ha,ha'⟩ := ha h.1
    obtain ⟨hb,hb'⟩ := hb h.2
    refine ⟨ha.mul hb,?_⟩
    convert! (ha'.mul hb).add (ha.mul hb') using 1
    dsimp [der,sec]
    ring
  | sq a ha =>
    obtain ⟨ha,ha'⟩ := ha h
    refine ⟨?_,?_⟩
    · convert! ha.pow 2 using 1
      dsimp [der,val]
      ring
    · convert! ((ha.const_mul 2).mul ha') using 1
      dsimp [der,sec]
      ring
  | inv a ha =>
    obtain ⟨ha,ha'⟩ := ha h.1
    have hi := ha.inv h.2
    refine ⟨?_,?_⟩
    · convert! hi using 1
      dsimp [val,der]
      field_simp
    · convert! ha'.neg.mul (hi.pow 2) using 1
      dsimp [der,sec]
      field_simp
      ring
  | exp a ha =>
    obtain ⟨ha,ha'⟩ := ha h
    refine ⟨ha.exp,?_⟩
    convert! ha.exp.mul ha' using 1
    dsimp [der,sec]
    ring
  | tanh a ha =>
    obtain ⟨ha,ha'⟩ := ha h
    have hm := (Calculus.hasDerivAt_tanh (a.val x)).comp x ha
    refine ⟨hm,?_⟩
    convert! ((hasDerivAt_const x (1:ℝ)).sub (hm.pow 2)).mul ha' using 1
    dsimp [der,sec]
    ring

lemma compute_sound (e : Expr) {B : Box} {J : Jet} (hc : e.compute B=some J)
    {x : ℝ} (hx : x ∈ B) :
    e.val x ∈ J.val ∧ e.der x ∈ J.der ∧ e.sec x ∈ J.sec ∧ e.Regular x := by
  induction e generalizing J with
  | rat q =>
    simp only [compute,Option.some.injEq] at hc
    cases hc
    exact ⟨Box.mem_rat q,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_zero] using Box.mem_rat 0,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_zero] using Box.mem_rat 0,trivial⟩
  | var =>
    simp only [compute,Option.some.injEq] at hc
    cases hc
    exact ⟨hx,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_one] using Box.mem_rat 1,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_zero] using Box.mem_rat 0,trivial⟩
  | add a b ha hb =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    obtain ⟨hb0,hb1,hb2,hbr⟩ := hb hC
    exact ⟨Box.mem_add ha0 hb0,Box.mem_add ha1 hb1,Box.mem_add ha2 hb2,har,hbr⟩
  | neg a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    exact ⟨Box.mem_neg ha0,Box.mem_neg ha1,Box.mem_neg ha2,har⟩
  | mul a b ha hb =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    obtain ⟨hb0,hb1,hb2,hbr⟩ := hb hC
    refine ⟨Box.mem_mul ha0 hb0,Box.mem_add (Box.mem_mul ha1 hb0) (Box.mem_mul ha0 hb1),?_,har,hbr⟩
    simpa only [sec,der,Jet.mul,Jet.sq,Rat.cast_ofNat,mul_assoc] using Box.mem_add
      (Box.mem_add (Box.mem_mul ha2 hb0) (Box.mem_mul (Box.mem_rat 2) (Box.mem_mul ha1 hb1))) (Box.mem_mul ha0 hb2)
  | sq a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    refine ⟨Box.mem_sq ha0,?_,?_,har⟩
    · simpa only [sec,der,Jet.mul,Jet.sq,Rat.cast_ofNat,mul_assoc] using Box.mem_mul (Box.mem_rat 2) (Box.mem_mul ha0 ha1)
    · exact Box.mem_mul (by simpa using Box.mem_rat 2) (Box.mem_add (Box.mem_sq ha1) (Box.mem_mul ha0 ha2))
  | inv a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Jet.inv,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    obtain ⟨hi,hn⟩ := Box.mem_inv ha0 hC
    refine ⟨hi,?_,?_,har,hn⟩
    · simpa only [der,neg_mul] using Box.mem_neg (Box.mem_mul ha1 (Box.mem_sq hi))
    · have h := Box.mem_sub (Box.mem_mul (Box.mem_rat 2) (Box.mem_mul (Box.mem_sq ha1)
          (Box.mem_mul hi (Box.mem_sq hi)))) (Box.mem_mul ha2 (Box.mem_sq hi))
      convert! h using 1
      dsimp [sec,Jet.inv]
      ring
  | exp a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Jet.exp,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    have he := Box.mem_exp ha0 hC
    exact ⟨he,Box.mem_mul he ha1,Box.mem_mul he (Box.mem_add ha2 (Box.mem_sq ha1)),har⟩
  | tanh a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Jet.tanh,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    have hm := Jet.mem_tanhBox ha0 hC
    have hv := Box.mem_sub (Box.mem_rat 1) (Box.mem_sq hm)
    norm_num only [Rat.cast_one] at hv
    refine ⟨hm,Box.mem_mul hv ha1,?_,har⟩
    have h := Box.mem_sub (Box.mem_mul hv ha2) (Box.mem_mul (Box.mem_rat 2)
      (Box.mem_mul hm (Box.mem_mul hv (Box.mem_sq ha1))))
    simpa only [sec,der,Jet.mul,Jet.sq,Rat.cast_ofNat,mul_assoc] using h

end Expr
end SKRatio.Certificate

end

end OAI
