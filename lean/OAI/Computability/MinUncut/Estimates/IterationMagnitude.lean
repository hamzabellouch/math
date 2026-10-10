import Mathlib
import OAI.Computability.MinUncut.Estimates.PolynomialRecursor

namespace OAI

namespace MinUncut.Costed.Arena

lemma iterate_length_maximum {f : List ℕ → List ℕ} (L M : ℕ)
    (hf : ∀v,(f v).length≤v.length+L ∧ maximum (f v)≤ maximum v+M) (v : List ℕ) (i : ℕ) :
    (f^[i] v).length≤v.length+L*i ∧ maximum (f^[i] v)≤ maximum v+M*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hh := hf (f^[i] v)
    simp only [Nat.mul_add,Nat.mul_one] at *
    constructor <;> omega

lemma iterate_magnitude {f : List ℕ → List ℕ} (L M : ℕ)
    (hf : ∀v,(f v).length≤v.length+L ∧ maximum (f v)≤ maximum v+M)
    (n : ℕ) (v : List ℕ) (i : ℕ) (hi : i≤n) :
    magnitude (f^[i] v)≤(L+1)*(M+1)*(magnitude (n::v)+1)^2 := by
  have hb := iterate_length_maximum L M hf v i
  have hl := length_le_magnitude v
  have hm := maximum_le_magnitude v
  have hs := magnitude_le_length_maximum (f^[i] v)
  have hin : i ≤ magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
  have h1 : (f^[i] v).length≤(L+1)*(magnitude (n::v)+1) := by
    have hh := Nat.mul_le_mul_left L hin
    simp only [magnitude_cons] at hh ⊢
    nlinarith
  have h2 : maximum (f^[i] v)+1≤(M+1)*(magnitude (n::v)+1) := by
    have hh := Nat.mul_le_mul_left M hin
    simp only [magnitude_cons] at hh ⊢
    nlinarith
  have h := Nat.mul_le_mul h1 h2
  nlinarith

noncomputable def PolyProgram.safeIterate {f : List ℕ → List ℕ} (F : PolyProgram f) (L M : ℕ)
    (hf : ∀v,(f v).length≤v.length+L ∧ maximum (f v)≤ maximum v+M) :
    PolyProgram (fun v=>f^[v.headI] v.tail) :=
  PolyProgram.iterate F (Polynomial.C ((L+1)*(M+1))*(Polynomial.X+1)^2) (by
    intro n v i hi
    simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using iterate_magnitude L M hf n v i hi)

end MinUncut.Costed.Arena

namespace MinUncut.Costed.Division
open Arena

def step (v : List ℕ) : List ℕ :=
  let q := (v.drop 0).headI
  let r := (v.drop 1).headI
  let d := (v.drop 2).headI
  if r+1=d then (q+1)::0::d::v.drop 3 else q::(r+1)::d::v.drop 3

noncomputable def stepProgram : PolyProgram step :=
  (PolyProgram.branch (Expr.eq (.add (.reg 1) (.const 1)) (.reg 2)).program
    ((Expr.reg 0).program.cons ((Expr.add (.reg 1) (.const 1)).program.cons
      ((Expr.reg 2).program.cons (PolyProgram.drop 3))))
    ((Expr.add (.reg 0) (.const 1)).program.cons ((PolyProgram.const 0).cons
      ((Expr.reg 2).program.cons (PolyProgram.drop 3))))).ofEq (by
    intro v
    simp only [Expr.eval,List.headI_cons,step]
    by_cases h : (v.drop 1).headI+1=(v.drop 2).headI <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero])

lemma step_safe (v : List ℕ) :
    (step v).length≤v.length+3 ∧ maximum (step v) ≤ maximum v+1 := by
  have h0 := reg_le_maximum v 0
  have h1 := reg_le_maximum v 1
  have h2 := reg_le_maximum v 2
  have h3 := maximum_drop v 3
  change (v.drop 0).headI≤_ at h0
  change (v.drop 1).headI≤_ at h1
  change (v.drop 2).headI≤_ at h2
  dsimp only [step]
  split_ifs <;> simp only [List.length_cons,List.length_drop,maximum_cons] <;>
    constructor <;> omega

lemma step_exact (n d : ℕ) (v : List ℕ) :
    step (n/d::n%d::d::v)=((n+1)/d)::((n+1)%d)::d::v := by
  by_cases hd : d=0
  · subst d
    simp [step]
  have hp : 0<d := by omega
  have hm := Nat.mod_lt n hp
  have hn : n=n/d*d+n%d := by simpa only [Nat.mul_comm] using (Nat.div_add_mod n d).symm
  by_cases hc : n%d+1=d
  · have he : n+1=(n/d+1)*d := by nlinarith
    simp only [step,List.drop_zero,List.headI_cons,List.drop_succ_cons,hc,ite_true,he,Nat.mul_div_cancel _ hp,Nat.mul_mod_left]
  · have he : n+1=n/d*d+(n%d+1) := by omega
    have hr : n%d+1<d := by omega
    simp only [step,List.drop_zero,List.headI_cons,List.drop_succ_cons,hc,ite_false,he]
    have hdv : (n/d*d+(n%d+1))/d=n/d := by
      rw [Nat.mul_comm (n/d) d,Nat.mul_add_div hp,Nat.div_eq_of_lt hr,Nat.add_zero]
    have hmd : (n/d*d+(n%d+1))%d=n%d+1 := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr]
    rw [hdv,hmd]

lemma iterate_exact (n d : ℕ) (v : List ℕ) :
    step^[n] (0::0::d::v)=n/d::n%d::d::v := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,step_exact]

noncomputable def pair : PolyProgram (fun v=>[v.headI/v.tail.headI,v.headI%v.tail.headI]) := by
  let pack := PolyProgram.head.cons ((PolyProgram.const 0).cons ((PolyProgram.const 0).cons
    ((PolyProgram.head.comp PolyProgram.tail).cons PolyProgram.nil)))
  let run := (PolyProgram.safeIterate stepProgram 3 1 step_safe).comp pack
  let take := (PolyProgram.projection 0).cons ((PolyProgram.projection 1).cons PolyProgram.nil)
  exact (take.comp run).ofEq (by
    intro v
    simp only [Function.comp_apply,List.headI_cons,List.tail_cons,iterate_exact,List.drop_zero,List.drop_one])

noncomputable def quotient : PolyProgram (fun v=>[v.headI/v.tail.headI]) :=
  (PolyProgram.head.comp pair).ofEq (by intro v; rfl)
noncomputable def remainder : PolyProgram (fun v=>[v.headI%v.tail.headI]) :=
  (PolyProgram.projection 1 |>.comp pair).ofEq (by intro v; rfl)

end MinUncut.Costed.Division

end OAI
