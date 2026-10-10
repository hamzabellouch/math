import OAI.Computability.RationalHitting.RationalArithmetic

namespace OAI

namespace RationalHitting.StackLanguage
open scoped BigOperators

lemma range_sum_fin {A : Type} [AddCommMonoid A] (n : ℕ) (f : ℕ → A) :
    ((List.range n).map f).sum=∑ i : Fin n, f i.val := by
  rw [range_map_to_finRange,←List.ofFn_eq_map,List.sum_ofFn]

lemma finEquiv_val {m : ℕ} [NeZero m] (i : Fin m) :
    ((ZMod.finEquiv m) i).val=i.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

lemma finEquiv_symm_val {m : ℕ} [NeZero m] (i : ZMod m) :
    ((ZMod.finEquiv m).symm i).val=i.val := by
  exact (finEquiv_val ((ZMod.finEquiv m).symm i)).symm.trans
    (congrArg ZMod.val ((ZMod.finEquiv m).apply_symm_apply i))

lemma finEquiv_cast {m : ℕ} [NeZero m] (i : Fin m) :
    (ZMod.finEquiv m) i=(i.val : ZMod m) := by
  apply ZMod.val_injective
  rw [finEquiv_val,ZMod.val_cast_of_lt i.isLt]

lemma range_sum_zmod {A : Type} [AddCommMonoid A] (m : ℕ) [NeZero m] (f : ZMod m → A) :
    ((List.range m).map (fun (k : ℕ) => f (k : ZMod m))).sum = ∑ k : ZMod m, f k := by
  calc
    _ = ∑ i : Fin m, f (i.val : ZMod m) := by
      simpa only [List.map_map,Function.comp_def] using
        range_sum_fin m (fun k => f (k : ZMod m))
    _ = _ := Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ (fun i => by
      change f (i.val : ZMod m)=f ((ZMod.finEquiv m) i)
      rw [finEquiv_cast])

lemma zmod_val_sub {m : ℕ} [NeZero m] (a b : ZMod m) :
    (a-b).val=(a.val+(m-b.val)%m)%m := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val']

lemma coordinate_vals (e : ℕ) (i : Fin (Generator.D e)) :
    (((Generator.coordinate e).symm i).1.val,((Generator.coordinate e).symm i).2.val)=
      (i.val/CyclotomicRing.degree e,i.val % CyclotomicRing.degree e) := by
  change (((ZMod.finEquiv (CyclotomicRing.dimension e))
    (finProdFinEquiv.symm i).1).val,(finProdFinEquiv.symm i).2.val)=_
  rw [finEquiv_val]
  rfl
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open scoped BigOperators

namespace Runtime

def taylorTerm (m : ℕ) (a t : ℤ) (i j r : ℕ) : ℤ :=
  ((-a)^(m-1-r-i)*((m-1-r).choose i : ℤ)) *
    (a^(j-r)*(j.choose r : ℤ))*t^r

def taylor (m : ℕ) (a t : ℤ) (i j : ℕ) : ℤ :=
  ((List.range m).map (fun r => taylorTerm m a t i j r)).sum

def padded (m N : ℕ) (a t : ℤ) (i j : ℕ) : ℤ :=
  if j<N then taylor m a t i j else 0

lemma taylor_eq (m : ℕ) (a t : ℤ) (i j : Fin m) :
    taylor m a t i.val j.val=IntegralTest.full m a t i j := by
  unfold taylor IntegralTest.full
  rw [range_sum_fin]
  apply Finset.sum_congr rfl
  intro r _
  simp [taylorTerm,Fin.val_rev,Nat.sub_sub,Nat.add_comm]

lemma padded_eq (m N : ℕ) (a t : ℤ) (i j : Fin m) :
    padded m N a t i.val j.val=IntegralTest.padded m N a t i j := by
  simp [padded,IntegralTest.padded,taylor_eq]

abbrev TaylorArgs := Unary×ℤ×ℤ×Unary×Unary

@[fun_prop] theorem taylorTerm_poly : Poly (fun a : TaylorArgs×Unary =>
    taylorTerm a.1.1.val a.1.2.1 a.1.2.2.1 a.1.2.2.2.1.val a.1.2.2.2.2.val a.2.val) := by
  change Poly (fun a : TaylorArgs×Unary =>
    (Unary.powInt (-a.1.2.1) (a.1.1-1-a.2-a.1.2.2.2.1)*
      Unary.choose (a.1.1-1-a.2) a.1.2.2.2.1)*
    (Unary.powInt a.1.2.1 (a.1.2.2.2.2-a.2)*Unary.choose a.1.2.2.2.2 a.2)*
    Unary.powInt a.1.2.2.1 a.2)
  fun_prop

@[fun_prop] theorem taylor_poly : Poly (fun a : TaylorArgs =>
    taylor a.1.val a.2.1 a.2.2.1 a.2.2.2.1.val a.2.2.2.2.val) := by
  exact Poly.sumUp (show Poly (fun a : TaylorArgs => a.1) by fun_prop) taylorTerm_poly

@[fun_prop] theorem padded_poly : Poly (fun a : Unary×TaylorArgs =>
    padded a.2.1.val a.1.val a.2.2.1 a.2.2.2.1 a.2.2.2.2.1.val a.2.2.2.2.2.val) := by
  have hc : Poly (fun a : Unary×TaylorArgs => Unary.ltb a.2.2.2.2.2 a.1) := by fun_prop
  have hf : Poly (fun a : Unary×TaylorArgs =>
    taylor a.2.1.val a.2.2.1 a.2.2.2.1 a.2.2.2.2.1.val a.2.2.2.2.2.val) :=
    taylor_poly.comp (show Poly (Prod.snd : Unary×TaylorArgs → TaylorArgs) from Poly.snd)
  exact (hc.cond hf (Poly.const 0)).of_eq (by intro a;simp [padded,Unary.ltb])

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

abbrev Params := Unary×Unary×Unary×Unary×Unary
namespace Params
abbrev n (p : Params) : ℕ := p.1.val
abbrev N (p : Params) : ℕ := p.2.1.val
abbrev m (p : Params) : ℕ := p.2.2.1.val
abbrev q (p : Params) : ℕ := p.2.2.2.1.val
abbrev H (p : Params) : ℕ := p.2.2.2.2.val

def of (n s : ℕ) : Params :=
  (⟨n⟩,⟨Parameters.N n s⟩,⟨Parameters.M n s⟩,
    ⟨CyclotomicRing.degree (Parameters.exponent n s)⟩,⟨Parameters.H n s⟩)
end Params

namespace Params
def BB (a : Unary) : Unary := ⟨Parameters.B a.val⟩
def DD (a : Unary×Unary) : Unary := ⟨Parameters.delta a.1.val a.2.val⟩
def threshold (a : Unary×Unary) : Unary := BB a.2 * DD a
def EE (a : Unary×Unary) : Unary := ⟨Parameters.exponent a.1.val a.2.val⟩
def MM (a : Unary×Unary) : Unary := ⟨Parameters.M a.1.val a.2.val⟩
def NN (a : Unary×Unary) : Unary := ⟨Parameters.N a.1.val a.2.val⟩
def HH (a : Unary×Unary) : Unary := ⟨Parameters.H a.1.val a.2.val⟩
def QQ (a : Unary×Unary) : Unary := ⟨CyclotomicRing.degree (Parameters.exponent a.1.val a.2.val)⟩
end Params
namespace Poly
@[fun_prop] theorem paramB : Poly Params.BB := by
  change Poly (fun a : Unary => 2*a+1)
  fun_prop
@[fun_prop] theorem paramDelta : Poly Params.DD := by
  change Poly (fun a : Unary×Unary => 2*(a.1+1)^3*(2*a.2+1))
  fun_prop
@[fun_prop] theorem paramThreshold : Poly Params.threshold := by
  unfold Params.threshold
  fun_prop
@[fun_prop] theorem paramExponent : Poly Params.EE := unaryLogTwo.comp paramThreshold
@[fun_prop] theorem paramM : Poly Params.MM := by
  exact (unaryNextPower.comp paramThreshold).of_eq (by
    intro a
    change Unary.mk (2^(Parameters.B a.2.val*Parameters.delta a.1.val a.2.val).size)=_
    simp only [Params.MM,Parameters.M,Parameters.exponent,
      nat_size_log (Parameters.threshold_pos a.1.val a.2.val)])
@[fun_prop] theorem paramN : Poly Params.NN := by
  change Poly (fun a : Unary×Unary => Params.MM a-Params.DD a)
  fun_prop
@[fun_prop] theorem paramH : Poly Params.HH := by
  change Poly (fun a : Unary×Unary => 1+3*(a.2+2)*Params.BB a.2*(Params.MM a)^3)
  fun_prop
@[fun_prop] theorem paramDegree : Poly Params.QQ := by
  have hh : Poly (fun a : Unary×Unary => Params.MM a/2) := by fun_prop
  exact hh.of_eq (by
    intro a
    change Unary.mk (Parameters.M a.1.val a.2.val/2)=_
    simp [Params.QQ,Parameters.M,CyclotomicRing.degree,pow_succ])
@[fun_prop] theorem params : Poly (fun a : Unary×Unary => Params.of a.1.val a.2.val) := by
  change Poly (fun a : Unary×Unary => (a.1,Params.NN a,Params.MM a,Params.QQ a,Params.HH a))
  fun_prop
end Poly
end RationalHitting.StackLanguage

end OAI
