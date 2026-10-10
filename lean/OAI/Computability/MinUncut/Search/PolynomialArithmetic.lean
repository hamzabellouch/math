import Mathlib
import OAI.Computability.MinUncut.Search.CodeArithmetic

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def pairPack : PolyProgram (fun v=>[v.headI,v.tail.headI]) :=
  head.cons ((head.comp tail).cons nil)

def binary (c : Code) (f : ℕ → ℕ → ℕ) (p : Polynomial ℕ)
    (hr : ∀a b,Runs c [a,b] [f a b] (p.eval (magnitude [a,b])))
    (hs : ∀a b,magnitude [f a b]≤p.eval (magnitude [a,b])) :
    PolyProgram (fun v=>[f v.headI v.tail.headI]) where
  code := .comp c pairPack.code
  bound := pairPack.bound+p.comp pairPack.bound+1
  run v := by
    have h := run_comp (pairPack.run v) (hr v.headI v.tail.headI)
    apply h.mono
    simp only [eval_add,eval_comp,eval_one]
    have h' := evalNat_mono p (pairPack.size v)
    omega
  size v := by
    have h := (hs v.headI v.tail.headI).trans (evalNat_mono p (pairPack.size v))
    simp only [eval_add,eval_comp,eval_one]
    omega

def add : PolyProgram (fun v=>[v.headI+v.tail.headI]) :=
  binary addCode (fun a b=>a+b) (C 100000*(X+2)^2)
    (by intro a b; simpa [Nat.add_comm] using run_add a b [])
    (by intro a b; simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,
                               eval_add,eval_X,eval_ofNat]; nlinarith)

def sub : PolyProgram (fun v=>[v.headI-v.tail.headI]) :=
  (binary subCode (fun a b=>b-a) (C 100000*(X+2)^2)
    (by intro a b; simpa using run_sub a b [])
    (by intro a b; simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,
                               eval_add,eval_X,eval_ofNat];
        have h : b-a≤b := Nat.sub_le ..
        have hp : b+1≤(a+1+(b+1+0)+2)^2 :=
          (by omega : b+1≤a+1+(b+1+0)+2).trans (Nat.le_self_pow (by omega) _)
        omega)).comp
      ((head.comp tail).cons (head.cons nil))

def mul : PolyProgram (fun v=>[v.headI*v.tail.headI]) :=
  binary mulCode (fun a b=>a*b) (C 10000000*(X+2)^6)
    (by intro a b; simpa [Nat.mul_comm] using run_mul a b [])
    (by intro a b
        simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,
          eval_add,eval_X,eval_ofNat]
        have h₁ : a*b+1≤(a+1+(b+1+0)+2)^2 := by nlinarith
        have h₂ : (a+1+(b+1+0)+2)^2≤(a+1+(b+1+0)+2)^6 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega)

def addOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[(f v).headI+(g v).headI]) := add.comp (F.cons (G.cons nil))
def subOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[(f v).headI-(g v).headI]) := sub.comp (F.cons (G.cons nil))
def mulOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[(f v).headI*(g v).headI]) := mul.comp (F.cons (G.cons nil))

def eqOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[if (f v).headI=(g v).headI then 1 else 0]) :=
  (branch (addOf (subOf F G) (subOf G F)) (const 1) (const 0)).ofEq (by
    intro v
    simp only [List.headI_cons]
    have h : (f v).headI-(g v).headI+((g v).headI-(f v).headI)=0 ↔
        (f v).headI=(g v).headI := by omega
    simp only [h]
    split_ifs <;> rfl)

def leOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[if (f v).headI≤(g v).headI then 1 else 0]) :=
  (branch (subOf F G) (const 1) (const 0)).ofEq (by
    intro v
    simp only [List.headI_cons,Nat.sub_eq_zero_iff_le]
    split_ifs <;> rfl)

end MinUncut.Costed.PolyProgram

end
end

end OAI
