import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.ExprLayout

namespace OAI


namespace DirectedFeedback.StackDSL
open Turing
variable {K S : Type} [DecidableEq K]
namespace Prim

def support : Prim K S → Finset K
  | .push k _ | .pop k _ | .peek k _ => {k}
  | .load _ => ∅

def restrict (p : Prim K S) (scope : Finset K) (h : p.support ⊆ scope) :
    Prim {k // k ∈ scope} S :=
  match p with
  | .push k f => .push ⟨k,h (by simp [support])⟩ f
  | .pop k f => .pop ⟨k,h (by simp [support])⟩ f
  | .peek k f => .peek ⟨k,h (by simp [support])⟩ f
  | .load f => .load f

end Prim

namespace Store

def restrict (s : Store K S) (scope : Finset K) : Store {k // k ∈ scope} S :=
  ⟨s.state,fun k => s.tape k.val⟩

theorem restrict_update (s : K → List Bool) (scope : Finset K) (k : K) (hk : k ∈ scope)
    (l : List Bool) :
    (fun j : {k // k ∈ scope} => Function.update s k l j.val) =
      Function.update (fun j : {k // k ∈ scope} => s j.val) ⟨k,hk⟩ l := by
  funext j
  by_cases h : j.val = k
  · have hj : j = ⟨k,hk⟩ := Subtype.ext h
    simp [hj]
  · have hj : j ≠ ⟨k,hk⟩ := fun he => h (congrArg Subtype.val he)
    simp [h,hj]

end Store

namespace Prim

theorem restrict_run (p : Prim K S) (scope : Finset K) (h : p.support ⊆ scope) (s : Store K S) :
    (p.restrict scope h).run (s.restrict scope) = (p.run s).restrict scope := by
  cases p <;> simp only [restrict,run,Store.restrict]
  · congr 1
    exact (Store.restrict_update ..).symm
  · congr 1
    exact (Store.restrict_update ..).symm

end Prim

namespace Code

def support : Code K S → Finset K
  | .atom p => p.support
  | .seq c d | .branch _ c d => c.support ∪ d.support
  | .scan k _ c => insert k c.support

def restrict (c : Code K S) (scope : Finset K) (h : c.support ⊆ scope) :
    Code {k // k ∈ scope} S :=
  match c with
  | .atom p => .atom (p.restrict scope h)
  | .seq c d => .seq (c.restrict scope (fun _ hm => h (by simp [support,hm])))
    (d.restrict scope (fun _ hm => h (by simp [support,hm])))
  | .branch f c d => .branch f (c.restrict scope (fun _ hm => h (by simp [support,hm])))
    (d.restrict scope (fun _ hm => h (by simp [support,hm])))
  | .scan k f c => .scan ⟨k,h (by simp [support])⟩ f
    (c.restrict scope (fun _ hm => h (by simp [support,hm])))

theorem Exec.restrict {c : Code K S} {s t : Store K S} {n : Nat} (h : c.Exec s n t)
    (scope : Finset K) (hc : c.support ⊆ scope) :
    (c.restrict scope hc).Exec (s.restrict scope) n (t.restrict scope) := by
  induction h with
  | atom p s =>
    rw [Code.restrict,← Prim.restrict_run p scope hc s]
    exact Exec.atom _ _
  | seq h1 h2 ih1 ih2 => exact Exec.seq (ih1 _) (ih2 _)
  | branch_true hb h ih => exact Exec.branch_true hb (ih _)
  | branch_false hb h ih => exact Exec.branch_false hb (ih _)
  | scan_nil hs =>
    apply Exec.scan_nil
    exact hs
  | @scan_cons k f c s t u b rest n m hs hb hl ihb ihl =>
    dsimp only [Code.restrict]
    apply Exec.scan_cons (s := s.restrict scope) (b := b) (rest := rest)
      (k := ⟨k,hc (by simp [support])⟩) (by exact hs)
    · have hh := ihb (fun _ hm => hc (by simp [support,hm]))
      convert hh using 1
      simp only [Store.restrict]
      congr 1
      exact (Store.restrict_update ..).symm
    · exact ihl hc

theorem restrict_ioStore (initial : S) (k : K) (bits : List Bool)
    (scope : Finset K) (hk : k ∈ scope) :
    (ioStore initial k bits).restrict scope = ioStore initial ⟨k,hk⟩ bits := by
  unfold Store.restrict ioStore
  congr 1
  funext j
  simp only [Subtype.ext_iff]

noncomputable def supportedComputation [Fintype S] {A B : Type}
    (ea : A → List Bool) (eb : B → List Bool) (f : A → B)
    (c : Code K S) (initial : S) (input output : K)
    (time : Polynomial Nat) (cost : A → Nat)
    (runs : ∀ a, c.Exec (ioStore initial input (ea a)) (cost a) (ioStore initial output (eb (f a))))
    (bound : ∀ a, cost a ≤ time.eval (ea a).length) :
    TM2ComputableInPolyTime ea eb f := by
  let scope := c.support ∪ {input,output}
  have hin : input ∈ scope := by simp [scope]
  have hout : output ∈ scope := by simp [scope]
  let d := c.restrict scope Finset.subset_union_left
  exact computation ea eb f d initial ⟨input,hin⟩ ⟨output,hout⟩ time cost (fun a => by
    have hh := (runs a).restrict scope Finset.subset_union_left
    simpa only [restrict_ioStore _ _ _ _ hin,restrict_ioStore _ _ _ _ hout] using hh) bound

end Code
end DirectedFeedback.StackDSL


namespace DirectedFeedback.BoundedExpr.Output
open StackDSL StackDSL.Code StackDSL.Ops
open Turing

def layout : Layout 0 where
  input := 0
  args := Fin.elim0
  output := 1
  fresh := 2
  input_lt := by omega
  args_lt := fun i => i.elim0
  output_lt := by omega
  input_ne := by omega
  args_ne := fun i => i.elim0

@[reducible] def program (o : Output 0) : Code Nat Bool :=
  .seq (o.compile 0 Fin.elim0 1 2) (.seq (clear 0) (transfer 1 0))

def steps (o : Output 0) (x : List Bool) : Nat :=
  o.cost x Fin.elim0+2*x.length+1+2*(o.eval x Fin.elim0).length+2

noncomputable def time (o : Output 0) : Polynomial Nat :=
  o.costBound+2*Polynomial.X+2*o.bound+3

theorem program_run (o : Output 0) (x : List Bool) :
    o.program.Exec (ioStore false 0 x) (o.steps x) (ioStore false 0 (o.eval x Fin.elim0)) := by
  let s := ioStore false (0 : Nat) x
  have hs : layout.Ready s x Fin.elim0 := by
    constructor
    · simp [layout,s,ioStore]
    · exact fun i => i.elim0
    · intro k hk
      change 2≤k at hk
      simp [s,ioStore,show k≠0 by omega]
  have h1 := o.correct layout x Fin.elim0 s hs
  simp only [layout] at h1
  have hs1 : s.tape 1 = [] := by simp [s,ioStore]
  rw [hs1,List.append_nil] at h1
  have hc := clear_run 0 ((s.put 1 (o.eval x Fin.elim0).reverse).flag false)
  have hcval : ((s.put 1 (o.eval x Fin.elim0).reverse).flag false).tape 0=x := by simp [s,ioStore]
  rw [hcval] at hc
  have ht := transfer_run (1 : Nat) 0 (by omega)
    (((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 [])
  have htv : (((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 []).tape 1 =
      (o.eval x Fin.elim0).reverse := by simp
  have ht0 : (((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 []).tape 0=[] := by simp
  rw [htv,ht0,List.length_reverse,List.reverse_reverse,List.append_nil] at ht
  have hend : (((((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 []).put 1 []).put
      0 (o.eval x Fin.elim0)).flag false = ioStore false 0 (o.eval x Fin.elim0) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk0 : k=0 <;> by_cases hk1 : k=1 <;> simp_all [Store.put,Store.flag,s,ioStore]
  rw [hend] at ht
  have hh := Exec.seq h1 (Exec.seq hc ht)
  convert hh using 1
  dsimp [steps]
  omega

theorem steps_le_time (o : Output 0) (x : List Bool) : o.steps x ≤ o.time.eval x.length := by
  have h1 := o.cost_le_bound x Fin.elim0 x.length (by omega) (fun i => i.elim0)
  have h2 := o.length_le_bound x Fin.elim0 x.length (by omega) (fun i => i.elim0)
  simp only [steps,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

noncomputable def computation (o : Output 0) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (fun x => o.eval x Fin.elim0) :=
  Code.supportedComputation id id (fun x => o.eval x Fin.elim0) o.program false 0 0
    o.time o.steps o.program_run o.steps_le_time

theorem computation_alphabet (o : Output 0) (k : o.computation.tm.K) : Finite (o.computation.tm.Γ k) := by
  change Finite Bool
  infer_instance

noncomputable def realizes {B : Type} (eb : B → List Bool) (f : List Bool → B)
    (o : Output 0) (h : ∀ x, o.eval x Fin.elim0 = eb (f x)) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) eb f where
  tm := o.computation.tm
  inputAlphabet := o.computation.inputAlphabet
  outputAlphabet := o.computation.outputAlphabet
  time := o.computation.time
  outputsFun x := by
    have hh := o.computation.outputsFun x
    simpa only [id_eq,h x] using hh

theorem realizes_alphabet {B : Type} (eb : B → List Bool) (f : List Bool → B)
    (o : Output 0) (h : ∀ x, o.eval x Fin.elim0 = eb (f x))
    (k : (realizes eb f o h).tm.K) : Finite ((realizes eb f o h).tm.Γ k) :=
  computation_alphabet o k

end DirectedFeedback.BoundedExpr.Output


namespace DirectedFeedback.BoundedExpr
open scoped BigOperators
namespace Expr

def rename {r s : Nat} (ρ : Fin r → Fin s) : Expr r → Expr s
  | .lit n => .lit n
  | .arg i => .arg (ρ i)
  | .length => .length
  | .bit i => .bit (rename ρ i)
  | .add a b => .add (rename ρ a) (rename ρ b)
  | .mul a b => .mul (rename ρ a) (rename ρ b)
  | .sub a b => .sub (rename ρ a) (rename ρ b)
  | .zero a => .zero (rename ρ a)
  | .sum b e => .sum (rename ρ b) (rename (Fin.cons 0 (fun i => (ρ i).succ)) e)

theorem eval_rename {r s : Nat} (ρ : Fin r → Fin s) (e : Expr r) (x : List Bool) (a : Fin s → Nat) :
    (e.rename ρ).eval x a = e.eval x (a ∘ ρ) := by
  induction e generalizing s with
  | lit n => rfl
  | arg i => rfl
  | length => rfl
  | bit i ih => simp [rename,eval,ih]
  | add a b iha ihb => simp [rename,eval,iha,ihb]
  | mul a b iha ihb => simp [rename,eval,iha,ihb]
  | sub a b iha ihb => simp [rename,eval,iha,ihb]
  | zero a ih => simp [rename,eval,ih]
  | sum b e ihb ihe =>
    simp only [rename,eval,ihb,ihe]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Function.comp_def]

def subst {r s : Nat} (ρ : Fin r → Expr s) : Expr r → Expr s
  | .lit n => .lit n
  | .arg i => ρ i
  | .length => .length
  | .bit i => .bit (subst ρ i)
  | .add a b => .add (subst ρ a) (subst ρ b)
  | .mul a b => .mul (subst ρ a) (subst ρ b)
  | .sub a b => .sub (subst ρ a) (subst ρ b)
  | .zero a => .zero (subst ρ a)
  | .sum b e => .sum (subst ρ b) (subst (Fin.cons (.arg 0) (fun i => (ρ i).rename Fin.succ)) e)

theorem eval_subst {r s : Nat} (ρ : Fin r → Expr s) (e : Expr r) (x : List Bool) (a : Fin s → Nat) :
    (e.subst ρ).eval x a = e.eval x (fun i => (ρ i).eval x a) := by
  induction e generalizing s with
  | lit n => rfl
  | arg i => rfl
  | length => rfl
  | bit i ih => simp [subst,eval,ih]
  | add a b iha ihb => simp [subst,eval,iha,ihb]
  | mul a b iha ihb => simp [subst,eval,iha,ihb]
  | sub a b iha ihb => simp [subst,eval,iha,ihb]
  | zero a ih => simp [subst,eval,ih]
  | sum b e ihb ihe =>
    simp only [subst,eval,ihb,ihe]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [eval]
    · simp [eval_rename,Function.comp_def]

end Expr

def Def {r : Nat} (f : List Bool → (Fin r → Nat) → Nat) : Prop :=
  ∃ e : Expr r, ∀ x a, e.eval x a = f x a

namespace Def
variable {r : Nat} {f g h : List Bool → (Fin r → Nat) → Nat}

theorem congr (hf : Def f) (he : ∀ x a, f x a = g x a) : Def g := by
  obtain ⟨e,he'⟩ := hf
  exact ⟨e,fun x a => (he' x a).trans (he x a)⟩

theorem lit (n : Nat) : Def (fun (_ : List Bool) (_ : Fin r → Nat) => n) := ⟨.lit n,fun _ _ => rfl⟩
theorem arg (i : Fin r) : Def (fun (_ : List Bool) a => a i) := ⟨.arg i,fun _ _ => rfl⟩
theorem length : Def (fun (x : List Bool) (_ : Fin r → Nat) => x.length) := ⟨.length,fun _ _ => rfl⟩
theorem bit (hf : Def f) : Def (fun x a => if x[f x a]?.getD false then 1 else 0) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨.bit e,by intro x a; simp only [Expr.eval,he]⟩
theorem add (hf : Def f) (hg : Def g) : Def (fun x a => f x a + g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.add e d,by intro x a; simp only [Expr.eval,he,hd]⟩
theorem mul (hf : Def f) (hg : Def g) : Def (fun x a => f x a * g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.mul e d,by intro x a; simp only [Expr.eval,he,hd]⟩
theorem sub (hf : Def f) (hg : Def g) : Def (fun x a => f x a - g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.sub e d,by intro x a; simp only [Expr.eval,he,hd]⟩
theorem zero (hf : Def f) : Def (fun x a => if f x a=0 then 1 else 0) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨.zero e,by intro x a; simp only [Expr.eval,he]⟩

theorem rename {s : Nat} (hf : Def f) (ρ : Fin r → Fin s) : Def (fun x a => f x (a ∘ ρ)) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e.rename ρ,fun x a => (e.eval_rename ρ x a).trans (he x _)⟩

theorem subst {s : Nat} (hf : Def f) (ρ : Fin r → List Bool → (Fin s → Nat) → Nat)
    (hρ : ∀ i, Def (ρ i)) : Def (fun x a => f x (fun i => ρ i x a)) := by
  classical
  choose terms hterms using hρ
  obtain ⟨e,he⟩ := hf
  refine ⟨e.subst terms,?_⟩
  intro x a
  rw [Expr.eval_subst]
  simpa only [hterms] using he x (fun i => ρ i x a)

theorem sum (hb : Def f) {e : List Bool → (Fin (r+1) → Nat) → Nat} (he : Def e) :
    Def (fun x a => ∑ i ∈ Finset.range (f x a), e x (Fin.cons i a)) := by
  obtain ⟨b,hb⟩ := hb; obtain ⟨e,he⟩ := he
  exact ⟨.sum b e,by intro x a; simp only [Expr.eval,hb,he]⟩

theorem eq (hf : Def f) (hg : Def g) : Def (fun x a => if f x a = g x a then 1 else 0) := by
  apply ((hf.sub hg).add (hg.sub hf)).zero.congr
  intro x a
  by_cases he : f x a = g x a
  · simp [he]
  · have hn : f x a - g x a + (g x a - f x a) ≠ 0 := by omega
    simp only [he,hn,ite_false]

theorem le (hf : Def f) (hg : Def g) : Def (fun x a => if f x a ≤ g x a then 1 else 0) := by
  apply (hf.sub hg).zero.congr
  intro x a
  simp only [Nat.sub_eq_zero_iff_le]

theorem lt (hf : Def f) (hg : Def g) : Def (fun x a => if f x a < g x a then 1 else 0) := by
  apply (hf.add (lit 1)).le hg |>.congr
  intro x a
  simp

theorem ite (ht : Def h) (hf : Def f) (hg : Def g) :
    Def (fun x a => if h x a = 0 then f x a else g x a) := by
  apply ((ht.zero.mul hf).add (ht.zero.zero.mul hg)).congr
  intro x a
  by_cases hh : h x a=0 <;> simp [hh]

theorem pow (hf : Def f) (n : Nat) : Def (fun x a => f x a ^ n) := by
  induction n with
  | zero => simpa using lit (r := r) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem poly (hf : Def f) (p : Polynomial Nat) : Def (fun x a => p.eval (f x a)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial k a => simpa only [Polynomial.eval_monomial] using (lit a).mul (hf.pow k)

theorem finset_sum {I : Type} (s : Finset I) (f : I → List Bool → (Fin r → Nat) → Nat)
    (hf : ∀ i ∈ s, Def (f i)) : Def (fun x a => ∑ i ∈ s, f i x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lit (r := r) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

theorem table (hf : Def f) (N : Nat) (t : Fin N → Nat) :
    Def (fun x a => if h : f x a < N then t ⟨f x a,h⟩ else 0) := by
  have hh := finset_sum Finset.univ (fun i : Fin N => fun x a => (if f x a=i.val then 1 else 0)*t i)
    (fun i _ => (hf.eq (lit i.val)).mul (lit (t i)))
  apply hh.congr
  intro x a
  by_cases h : f x a<N
  · rw [dite_eq_left h]
    rw [Finset.sum_eq_single (⟨f x a,h⟩ : Fin N)]
    · simp
    · intro b hb hne
      simp [show f x a ≠ b.val from fun he => hne (Fin.ext he.symm)]
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro i hi
    simp [show f x a ≠ i.val by have := i.isLt; omega]

end Def
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr
open scoped BigOperators
namespace Def
variable {r : Nat} {f g : List Bool → (Fin r → Nat) → Nat}

theorem div (hf : Def f) (hg : Def g) : Def (fun x a => f x a / g x a) := by
  have hf' := hf.rename Fin.succ
  have hg' := hg.rename Fin.succ
  have hi : Def (fun (_ : List Bool) (a : Fin (r+1) → Nat) => a 0) := arg 0
  have hlo := (hi.mul hg').le hf'
  have hhi := hf'.lt ((hi.add (lit 1)).mul hg')
  have hh := (hf.add (lit 1)).sum (hi.mul (hlo.mul hhi))
  apply hh.congr
  intro x a
  simp only [Function.comp_def,Fin.cons_zero,Fin.cons_succ]
  by_cases hg0 : g x a=0
  · simp [hg0]
  · have hgpos : 0<g x a := Nat.pos_of_ne_zero hg0
    have hquot : f x a / g x a < f x a+1 := Nat.lt_succ_of_le (Nat.div_le_self ..)
    rw [Finset.sum_eq_single (f x a/g x a)]
    · have h1 : f x a / g x a * g x a ≤ f x a := Nat.div_mul_le_self ..
      have h2 : f x a < (f x a/g x a+1)*g x a :=
        (Nat.div_lt_iff_lt_mul hgpos).mp (by omega)
      simp [h1,h2]
    · intro i hi hne
      by_cases h1 : i*g x a ≤ f x a
      · by_cases h2 : f x a < (i+1)*g x a
        · have hle := (Nat.le_div_iff_mul_le hgpos).mpr h1
          have hlt := (Nat.div_lt_iff_lt_mul hgpos).mpr h2
          omega
        · simp [h2]
      · simp [h1]
    · simp [hquot]

theorem mod (hf : Def f) (hg : Def g) : Def (fun x a => f x a % g x a) := by
  apply (hf.sub ((hf.div hg).mul hg)).congr
  intro x a
  exact (Nat.mod_eq_sub_div_mul ..).symm

theorem min (hf : Def f) (hg : Def g) : Def (fun x a => min (f x a) (g x a)) := by
  apply (hf.sub (hf.sub hg)).congr
  intro x a
  omega

theorem max (hf : Def f) (hg : Def g) : Def (fun x a => max (f x a) (g x a)) := by
  apply (hf.add (hg.sub hf)).congr
  intro x a
  omega

end Def
end DirectedFeedback.BoundedExpr


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr

def FDef {r : Nat} {A : Type} (f : List Bool → (Fin r → Nat) → A) : Prop :=
  ∀ v, Def (fun x a => if f x a=v then 1 else 0)

namespace FDef
variable {r : Nat} {A B : Type} {f g : List Bool → (Fin r → Nat) → A}

theorem congr (hf : FDef f) (h : ∀ x a, f x a=g x a) : FDef g := by
  intro v
  apply (hf v).congr
  intro x a
  rw [h]

theorem const (v : A) : FDef (fun (_ : List Bool) (_ : Fin r → Nat) => v) := by
  intro w
  exact Def.lit (if v=w then 1 else 0)

theorem rename {s : Nat} (hf : FDef f) (ρ : Fin r → Fin s) : FDef (fun x a => f x (a ∘ ρ)) :=
  fun v => (hf v).rename ρ

theorem subst {s : Nat} (hf : FDef f) (ρ : Fin r → List Bool → (Fin s → Nat) → Nat)
    (hρ : ∀ i, Def (ρ i)) : FDef (fun x a => f x (fun i => ρ i x a)) :=
  fun v => (hf v).subst ρ hρ

theorem bind [Fintype A] (hf : FDef f)
    {g : A → List Bool → (Fin r → Nat) → B} (hg : ∀ v, FDef (g v)) :
    FDef (fun x a => g (f x a) x a) := by
  intro v
  have hh := Def.finset_sum Finset.univ
    (fun c : A => fun x a => (if f x a=c then 1 else 0)*(if g c x a=v then 1 else 0))
    (fun c _ => (hf c).mul (hg c v))
  apply hh.congr
  intro x a
  simp only [ite_mul, one_mul, zero_mul]
  simp

theorem map [Fintype A] (hf : FDef f) (t : A → B) : FDef (fun x a => t (f x a)) :=
  hf.bind (fun c => const (t c))

theorem toDef [Fintype A] (hf : FDef f) (t : A → Nat) : Def (fun x a => t (f x a)) := by
  have hh := Def.finset_sum Finset.univ
    (fun c : A => fun x a => (if f x a=c then 1 else 0)*t c)
    (fun c _ => (hf c).mul (Def.lit (t c)))
  apply hh.congr
  intro x a
  simp

theorem ite {h : List Bool → (Fin r → Nat) → Nat} (hh : Def h) (hf : FDef f) (hg : FDef g) :
    FDef (fun x a => if h x a=0 then f x a else g x a) := by
  intro v
  apply (hh.ite (hf v) (hg v)).congr
  intro x a
  split <;> simp_all

theorem bool {b : List Bool → (Fin r → Nat) → Bool}
    (h : Def (fun x a => if b x a then 1 else 0)) : FDef b := by
  intro v
  cases v with
  | true =>
    apply h.congr
    intro x a
    cases b x a <;> simp
  | false =>
    apply h.zero.congr
    intro x a
    cases b x a <;> simp

theorem decide {p : List Bool → (Fin r → Nat) → Prop}
    (h : Def (fun x a => if p x a then 1 else 0)) : FDef (fun x a => decide (p x a)) := by
  apply bool
  simpa

theorem ofNat {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (N : Nat) (t : Fin N → A)
    (default : A) : FDef (fun x a => if h : n x a<N then t ⟨n x a,h⟩ else default) := by
  intro v
  have hh := (hn.lt (Def.lit N)).ite (Def.lit (if default=v then 1 else 0))
    (hn.table N (fun i => if t i=v then 1 else 0))
  apply hh.congr
  intro x a
  by_cases h : n x a<N <;> simp [h]

theorem pair [Fintype A] [Fintype B] (hf : FDef f)
    {g : List Bool → (Fin r → Nat) → B} (hg : FDef g) :
    FDef (fun x a => (f x a,g x a)) :=
  hf.bind (fun c => hg.map (Prod.mk c))

theorem pi {I : Type} [Fintype I] {F : I → Type} [∀ i, Fintype (F i)]
    {f : ∀ i, List Bool → (Fin r → Nat) → F i} (hf : ∀ i, FDef (f i)) :
    FDef (fun x a => fun i => f i x a) := by
  intro v
  have hsum := Def.finset_sum Finset.univ
    (fun i : I => fun x a => if f i x a = v i then 0 else 1)
    (fun i _ => (hf i (v i)).zero.congr (by intro x a; split <;> simp_all))
  apply hsum.zero.congr
  intro x a
  have he : (∑ i, if f i x a = v i then 0 else 1 : Nat)=0 ↔ (fun i => f i x a)=v := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    simp only [Finset.mem_univ,true_implies,ite_eq_left_iff,one_ne_zero,imp_false,not_not]
    exact funext_iff.symm
  by_cases h : (fun i => f i x a)=v <;> simp_all

end FDef
end DirectedFeedback.BoundedExpr

end


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr

def PDef {r : Nat} (p : List Bool → (Fin r → Nat) → Prop) : Prop :=
  Def (fun x a => if p x a then 1 else 0)

namespace PDef
variable {r : Nat} {p q : List Bool → (Fin r → Nat) → Prop}

theorem congr (hp : PDef p) (h : ∀ x a, p x a ↔ q x a) : PDef q :=
  Def.congr hp (fun x a => by simp only [h x a])

theorem const (p : Prop) : PDef (fun (_ : List Bool) (_ : Fin r → Nat) => p) :=
  Def.lit (if p then 1 else 0)

theorem not (hp : PDef p) : PDef (fun x a => ¬p x a) := by
  apply Def.congr (Def.zero hp)
  intro x a
  by_cases h : p x a <;> simp [h]

theorem and (hp : PDef p) (hq : PDef q) : PDef (fun x a => p x a ∧ q x a) := by
  apply Def.congr (Def.mul hp hq)
  intro x a
  by_cases h : p x a <;> by_cases h' : q x a <;> simp [h,h']

theorem or (hp : PDef p) (hq : PDef q) : PDef (fun x a => p x a ∨ q x a) := by
  exact (hp.not.and hq.not).not.congr (by intro x a; tauto)

theorem imp (hp : PDef p) (hq : PDef q) : PDef (fun x a => p x a → q x a) := by
  exact (hp.not.or hq).congr (by intro x a; tauto)

theorem all {I : Type} [Fintype I] {p : I → List Bool → (Fin r → Nat) → Prop}
    (hp : ∀ i, PDef (p i)) : PDef (fun x a => ∀ i, p i x a) := by
  have hh := (Def.finset_sum Finset.univ (fun i : I => fun x a => if ¬p i x a then 1 else 0)
    (fun i _ => Def.congr (hp i).not (by intro x a; by_cases h : p i x a <;> simp [h]))).zero
  apply hh.congr
  intro x a
  have he : (∑ i, if ¬p i x a then 1 else 0 : Nat)=0 ↔ ∀ i, p i x a := by
    simp
  by_cases h : ∀ i, p i x a <;> simp_all

theorem exists_fin {I : Type} [Fintype I] {p : I → List Bool → (Fin r → Nat) → Prop}
    (hp : ∀ i, PDef (p i)) : PDef (fun x a => ∃ i, p i x a) := by
  exact ((all (fun i => (hp i).not)).not).congr (by intro x a; simp)

theorem eq {A : Type} [Fintype A] {f g : List Bool → (Fin r → Nat) → A}
    (hf : FDef f) (hg : FDef g) : PDef (fun x a => f x a=g x a) :=
  (hf.pair hg).toDef (fun z => if z.1=z.2 then 1 else 0)

theorem nat_eq {f g : List Bool → (Fin r → Nat) → Nat} (hf : Def f) (hg : Def g) :
    PDef (fun x a => f x a=g x a) := Def.congr (hf.eq hg) (by intro x a; by_cases h : f x a=g x a <;> simp [h])

theorem le {f g : List Bool → (Fin r → Nat) → Nat} (hf : Def f) (hg : Def g) :
    PDef (fun x a => f x a≤g x a) := Def.congr (hf.le hg) (by intro x a; by_cases h : f x a≤g x a <;> simp [h])

theorem lt {f g : List Bool → (Fin r → Nat) → Nat} (hf : Def f) (hg : Def g) :
    PDef (fun x a => f x a<g x a) := Def.congr (hf.lt hg) (by intro x a; by_cases h : f x a<g x a <;> simp [h])

theorem decide (hp : PDef p) : FDef (fun x a => decide (p x a)) := FDef.decide hp

theorem ite {A : Type} {f g : List Bool → (Fin r → Nat) → A}
    (hp : PDef p) (hf : FDef f) (hg : FDef g) : FDef (fun x a => if p x a then f x a else g x a) := by
  apply (FDef.ite hp hg hf).congr
  intro x a
  by_cases h : p x a <;> simp [h]

theorem nite {f g : List Bool → (Fin r → Nat) → Nat}
    (hp : PDef p) (hf : Def f) (hg : Def g) : Def (fun x a => if p x a then f x a else g x a) := by
  apply (Def.ite hp hg hf).congr
  intro x a
  by_cases h : p x a <;> simp [h]

end PDef

namespace FDef
variable {r : Nat} {A : Type} [Fintype A]

theorem select {N : Nat} {f : Fin N → List Bool → (Fin r → Nat) → A}
    (hf : ∀ i, FDef (f i)) {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (default : A) :
    FDef (fun x a => if h : n x a<N then f ⟨n x a,h⟩ x a else default) := by
  exact (FDef.pi hf).bind (fun table => hn |> fun hn => FDef.ofNat hn N table default)

theorem bool_true {f : List Bool → (Fin r → Nat) → Bool} (hf : FDef f) :
    PDef (fun x a => f x a=true) := hf true

end FDef
end DirectedFeedback.BoundedExpr

end


noncomputable section
open scoped Classical
namespace DirectedFeedback.DigitCodec
open BoundedExpr

def encode (b : Nat) : {L : Nat} → (Fin L → Nat) → Nat
  | 0,_ => 0
  | _+1,a => a 0+b*encode b (Fin.tail a)

def decode (b : Nat) : (L : Nat) → Nat → Fin L → Nat
  | 0,_ => Fin.elim0
  | L+1,n => Fin.cons (n%b) (decode b L (n/b))

theorem decode_lt (b : Nat) (hb : 0<b) (L n : Nat) (i : Fin L) : decode b L n i<b := by
  induction L generalizing n with
  | zero => exact i.elim0
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.mod_lt _ hb
    · exact ih (n/b) j

theorem encode_lt (b : Nat) (_hb : 0<b) {L : Nat} (a : Fin L → Nat) (ha : ∀ i, a i<b) :
    encode b a < b^L := by
  induction L with
  | zero => simp [encode]
  | succ L ih =>
    have ht := ih (Fin.tail a) (fun i => ha i.succ)
    have h0 := ha 0
    simp only [encode,pow_succ]
    nlinarith

theorem decode_encode (b : Nat) (hb : 0<b) {L : Nat} (a : Fin L → Nat) (ha : ∀ i,a i<b) :
    decode b L (encode b a)=a := by
  induction L with
  | zero => funext i; exact i.elim0
  | succ L ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [decode,encode,Nat.add_mod,Nat.mod_eq_of_lt (ha 0)]
    · have he : (a 0+b*encode b (Fin.tail a))/b=encode b (Fin.tail a) := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (ha 0),zero_add]
      change decode b L ((a 0+b*encode b (Fin.tail a))/b) j=a j.succ
      rw [he]
      exact congrFun (ih (Fin.tail a) (fun i => ha i.succ)) j

theorem encode_decode (b : Nat) (hb : 0<b) (L n : Nat) (hn : n<b^L) :
    encode b (decode b L n)=n := by
  induction L generalizing n with
  | zero => simp only [pow_zero] at hn; simp [encode,show n=0 by omega]
  | succ L ih =>
    have ht : n/b<b^L := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      simpa [pow_succ] using hn
    simp only [decode,encode,Fin.cons_zero,Fin.tail_cons,ih (n/b) ht]
    exact Nat.mod_add_div n b

noncomputable def equiv (b : Nat) (hb : 0<b) (L : Nat) : (Fin L → Fin b) ≃ Fin (b^L) where
  toFun a := ⟨encode b (fun i => (a i).val),encode_lt b hb _ (fun i => (a i).isLt)⟩
  invFun n := fun i => ⟨decode b L n.val i,decode_lt b hb L n.val i⟩
  left_inv a := by
    funext i
    apply Fin.ext
    exact congrFun (decode_encode b hb (fun i => (a i).val) (fun i => (a i).isLt)) i
  right_inv n := by apply Fin.ext; exact encode_decode b hb L n.val n.isLt

theorem decode_def {r : Nat} {b n : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hn : Def n) (L : Nat) (i : Fin L) :
    Def (fun x a => decode (b x a) L (n x a) i) := by
  induction L generalizing n with
  | zero => exact i.elim0
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hn.mod hb
    · exact ih (hn.div hb) j

end DirectedFeedback.DigitCodec

end


noncomputable section
open scoped Classical
namespace DirectedFeedback.BoxCodec
open BoundedExpr
variable (Tag : Type) [Fintype Tag] [Nonempty Tag]
variable (b C L : Nat) (hb : 0<b)

abbrev Box := Tag × ((Fin L → Fin b) × Fin C)
def size : Nat := Fintype.card Tag*(b^L*C)
def equiv : Box Tag b C L ≃ Fin (size Tag b C L) :=
  (Equiv.prodCongr (Fintype.equivFin Tag)
    ((Equiv.prodCongr (DigitCodec.equiv b hb L) (Equiv.refl (Fin C))).trans finProdFinEquiv)).trans
    finProdFinEquiv

def tag (i : Nat) : Tag :=
  if h : i/(b^L*C)<Fintype.card Tag then (Fintype.equivFin Tag).symm ⟨i/(b^L*C),h⟩
  else Classical.choice inferInstance
def digits (i : Nat) : Fin L → Nat := DigitCodec.decode b L ((i%(b^L*C))/C)
def copy (i : Nat) : Nat := (i%(b^L*C))%C

theorem tag_equiv (a : Box Tag b C L) : tag Tag b C L (equiv Tag b C L hb a).val=a.1 := by
  have h := (equiv Tag b C L hb).left_inv a
  have he := congrArg Prod.fst h
  have hi : ((equiv Tag b C L hb a).val/(b^L*C))<Fintype.card Tag :=
    (finProdFinEquiv.symm (equiv Tag b C L hb a)).1.isLt
  rw [tag,dite_eq_left hi]
  exact he

omit [Nonempty Tag] in
theorem digits_equiv (a : Box Tag b C L) (j : Fin L) :
    digits b C L (equiv Tag b C L hb a).val j=(a.2.1 j).val := by
  have h := (equiv Tag b C L hb).left_inv a
  have he := congrArg (fun z : Box Tag b C L => (z.2.1 j).val) h
  exact he

omit [Nonempty Tag] in
theorem copy_equiv (a : Box Tag b C L) :
    copy b C L (equiv Tag b C L hb a).val=a.2.2.val := by
  have h := (equiv Tag b C L hb).left_inv a
  exact congrArg (fun z : Box Tag b C L => z.2.2.val) h

theorem decode_tag (i : Fin (size Tag b C L)) :
    tag Tag b C L i.val=((equiv Tag b C L hb).symm i).1 := by
  simpa using tag_equiv Tag b C L hb ((equiv Tag b C L hb).symm i)
omit [Nonempty Tag] in
theorem decode_digits (i : Fin (size Tag b C L)) (j : Fin L) :
    digits b C L i.val j=(((equiv Tag b C L hb).symm i).2.1 j).val := by
  simpa using digits_equiv Tag b C L hb ((equiv Tag b C L hb).symm i) j
omit [Nonempty Tag] in
theorem decode_copy (i : Fin (size Tag b C L)) :
    copy b C L i.val=((equiv Tag b C L hb).symm i).2.2.val := by
  simpa using copy_equiv Tag b C L hb ((equiv Tag b C L hb).symm i)

variable {b C L}
theorem tag_def {r : Nat} {b C i : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hC : Def C) (hi : Def i) (L : Nat) :
    FDef (fun x a => tag Tag (b x a) (C x a) L (i x a)) := by
  exact FDef.ofNat (hi.div ((hb.pow L).mul hC)) _ (Fintype.equivFin Tag).symm (Classical.choice inferInstance)
theorem digits_def {r : Nat} {b C i : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hC : Def C) (hi : Def i) (L : Nat) (j : Fin L) :
    Def (fun x a => digits (b x a) (C x a) L (i x a) j) :=
  DigitCodec.decode_def hb ((hi.mod ((hb.pow L).mul hC)).div hC) L j
theorem copy_def {r : Nat} {b C i : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hC : Def C) (hi : Def i) (L : Nat) :
    Def (fun x a => copy (b x a) (C x a) L (i x a)) :=
  (hi.mod ((hb.pow L).mul hC)).mod hC

end DirectedFeedback.BoxCodec

end

end OAI
