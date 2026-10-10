import OAI.Geometry.Convex.GeneralMahler.Intervals.Basic

namespace OAI
/-! Real and interval towers of higher derivatives. -/
open Set Filter
open scoped Topology
namespace GeneralMahler.Jet
abbrev J (α:Type*) := ℕ → α
def tail {α} (x:J α): J α:=fun n=>x (n+1)
def ray {α} [Zero α] (x:α):J α
  | 0=>x
  | _+1=>0
def plusJ {α} [Add α] (x y:J α):J α:=fun n=>x n+y n
def subJ {α} [Sub α] (x y:J α):J α:=fun n=>x n-y n
def negJ {α} [Neg α] (x:J α):J α:=fun n=> -x n

def mulJ0 {α} [Add α] [Mul α] : ℕ→ J α→J α→α
  | 0,x,y=> x 0*y 0
  | n+1,x,y=> mulJ0 n (tail x) y+mulJ0 n x (tail y)
def mulJ {α} [Add α] [Mul α] (x y:J α):J α := fun n=> mulJ0 n x y

-- returns derivative of f(x)*y with f derivatives supplied by w
def cpM {α} [Add α] [Mul α]: ℕ→J α→J α→J α→α
  | 0,w,_,y=> w 0*y 0
  | n+1,w,x,y=> cpM n (tail w) x (mulJ (tail x) y) + cpM n w x (tail y)
def compJ {α} [Add α] [Mul α] (w x:J α):J α
  | 0=> w 0
  | n+1=> cpM n (tail w) x (tail x)

-- pointwise tower of derivative functions on S
abbrev RF:=ℝ→J ℝ
def TW (S:Set ℝ) (X:RF) : Prop :=
  ∀ n:ℕ,∀ x∈S, HasDerivAt (fun x=>X x n) (X x (n+1)) x
variable {S T:Set ℝ} {X Y W:RF}

lemma TW.mono (h:TW T X) (he:S⊆T): TW S X := fun n x hx=>h n x (he hx)
lemma TW.tail (h:TW S X): TW S fun x=>Jet.tail (X x) := fun n x hx=>h (n+1) x hx
lemma TW.add (h:TW S X) (g:TW S Y): TW S fun x=>plusJ (X x) (Y x) :=
  fun n x hx=>(h n x hx).fun_add (g n x hx)
lemma TW.sub (h:TW S X) (g:TW S Y): TW S fun x=>subJ (X x) (Y x) :=
  fun n x hx=>(h n x hx).fun_sub (g n x hx)
lemma TW.neg (h:TW S X): TW S fun x=>negJ (X x) := fun n x hx=>(h n x hx).neg
lemma TW.const (a:ℝ) : TW S fun _=>ray a := by
  intro n x hx; cases n with
  | zero=> exact hasDerivAt_const x a
  | succ n=> exact hasDerivAt_const x (0:ℝ)
lemma TW.mul (h:TW S X) (g:TW S Y): TW S fun x=>mulJ (X x) (Y x) := by
  intro n x hx; induction n generalizing X Y with
  | zero=> exact (h 0 x hx).fun_mul (g 0 x hx)
  | succ n ih=>
    exact (ih h.tail g).fun_add (ih h g.tail)

lemma TW.cp (h:TW S X) (g:TW T W) (hh:TW S Y) (he:∀ x∈S,X x 0∈T):
    TW S fun x n=> cpM n (W (X x 0)) (X x) (Y x) := by
  intro n x hx
  induction n generalizing Y W with
  | zero=>
    have ha := ((g 0 (X x 0) (he x hx)).comp x (h 0 x hx)).fun_mul (hh 0 x hx)
    convert ha using 1
    all_goals first|rfl| (simp only [cpM,Jet.tail,mulJ,mulJ0,Function.comp_apply]; ring)
  | succ n ih=>
    exact (ih g.tail (h.tail.mul hh)).fun_add (ih g hh.tail)
lemma TW.comp (h:TW S X) (g:TW T W) (he:∀ x∈S,X x 0∈T):
    TW S fun x=>compJ (W (X x 0)) (X x) := by
  intro n x hx; cases n with
  | zero=> exact (g 0 _ (he x hx)).comp x (h 0 x hx)
  | succ n=> exact TW.cp h g.tail h.tail he n x hx

noncomputable def dV (f:ℝ→ℝ): ℕ → ℝ →ℝ
  | 0=>f
  | n+1=>deriv (dV f n)
lemma V_eq (h:TW S X) (hs:IsOpen S) (n:Nat):
    EqOn (dV (fun x=>X x 0) n) (fun x=>X x n) S := by
  induction n with
  | zero=> exact fun _ _=>rfl
  | succ n ih=>
    intro x hx
    change deriv (dV _ n) _ = _
    have he : dV (fun x=>X x 0) n =ᶠ[𝓝 x] (fun x=>X x n) :=
      (show ∀ᶠ y in 𝓝 x,y∈S from hs.mem_nhds hx).mono fun y hy=> ih hy
    exact (he.deriv_eq).trans (h n x hx).deriv

open Cert Cert.IV
instance : Zero IV := ⟨IV.c 0⟩
def Fits (X:J ℝ) (A:J IV):Prop:=∀ n,X n∈A n
variable {U V F:J ℝ} {A B C:J IV}
lemma Fits.ray {x:ℝ} {a:IV} (h:x∈a): Fits (Jet.ray x) (Jet.ray a) := by
  intro n; cases n with
  | zero=>exact h
  | succ n=>exact mz
lemma Fits.drop (h:Fits U A): Fits (tail U) (tail A) := fun n=> h (n+1)
lemma Fits.add (h:Fits U A) (g:Fits V B) : Fits (plusJ U V) (plusJ A B) :=
  fun n=> madd (h n) (g n)
lemma Fits.sub (h:Fits U A) (g:Fits V B) : Fits (subJ U V) (subJ A B) :=
  fun n=> msub (h n) (g n)
lemma Fits.neg (h:Fits U A): Fits (negJ U) (negJ A):= fun n=> mneg (h n)
lemma Fits.mul (h:Fits U A) (g:Fits V B): Fits (mulJ U V) (mulJ A B) := by
  intro n; induction n generalizing U V A B with
  | zero=> exact mmul (h 0) (g 0)
  | succ n ih=> exact madd (ih h.drop g) (ih h g.drop)
lemma Fits.cp (h:Fits U A) (g:Fits V B) (hh:Fits F C) (n:ℕ):
    cpM n F U V∈ cpM n C A B := by
  induction n generalizing F V C B with
  | zero=> exact mmul (hh 0) (g 0)
  | succ n ih=> exact madd (ih (h.drop.mul g) hh.drop) (ih g.drop hh)
lemma Fits.comp (h:Fits U A) (g:Fits F C): Fits (compJ F U) (compJ C A) := by
  intro n; cases n with
  | zero=> exact g 0
  | succ n=> exact Fits.cp h h.drop g.drop n
end GeneralMahler.Jet

end OAI
