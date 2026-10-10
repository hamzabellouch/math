import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.RegisterOperators

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary.Decrement
open Program
abbrev K := Fin 3

def store (xs out : List Bool) (b : Bool) : Store K := ![xs.reverse,out,[b]]
def partialStore (xs out : List Bool) : Store K := ![xs.reverse,out,[]]
def low (a b : Bool) := a ^^ b
def borrow (a b : Bool) := (!a) && b
lemma bit_equation (a b : Bool) : Add.bit a+2*Add.bit (borrow a b)=Add.bit (low a b)+Add.bit b := by
  cases a <;> cases b <;> decide

def step (a : Bool) : Program K := .pop 2 (fun b =>
  .seq (.push 1 (low a (b.getD false))) (.push 2 (borrow a (b.getD false))))
def pass : Program K := .loop 0 step
def program : Program K := .seq pass (move 1 0)
def scan : List Bool → Bool → List Bool × Bool
  | [],b => ([],b)
  | a::xs,b => let t := scan xs (borrow a b); (low a b::t.1,t.2)

lemma step_run (xs out : List Bool) (a b : Bool) :
    Run (step a) (store xs out b) 3 (store xs (out++[low a b]) (borrow a b)) := by
  have h1 := Run.push (partialStore xs out) (1:K) (low a b)
  let t := Function.update (partialStore xs out) 1 (out++[low a b])
  have hx : Run (.push (1:K) (low a b)) (partialStore xs out) 1 t := by simpa [partialStore,t] using h1
  have h2 := Run.push t (2:K) (borrow a b)
  have he2 : Function.update t 2 (t 2++[borrow a b])=store xs (out++[low a b]) (borrow a b) := by
    funext k;fin_cases k <;> simp [t,partialStore,store]
  rw [he2] at h2
  have hs := Run.seq _ _ _ _ _ _ _ hx h2
  unfold step
  refine Run.pop (store xs out b) (2:K) _ 2 _ ?_
  change Run (.seq (.push 1 (low a b)) (.push 2 (borrow a b)))
    (Function.update (store xs out b) 2 []) 2 _
  have he : Function.update (store xs out b) 2 []=partialStore xs out := by funext k;fin_cases k <;> simp [store,partialStore]
  rw [he];exact hs

lemma pass_run (xs out : List Bool) (b : Bool) :
    Run pass (store xs out b) (4*xs.length+1) (store [] (out++(scan xs b).1) (scan xs b).2) := by
  induction xs generalizing out b with
  | nil => simpa [pass,scan] using Run.loop_nil (store [] out b) (0:K) step (by rfl)
  | cons a xs ih =>
    have he : Function.update (store (a::xs) out b) 0 xs.reverse=store xs out b := by
      funext k;fin_cases k <;> simp [store]
    have hb := step_run xs out a b
    have ht := ih (out++[low a b]) (borrow a b)
    have H := Run.loop_cons (store (a::xs) out b) (0:K) step xs.reverse a _ _ 3 (4*xs.length+1)
      (by simp [store]) (by rw [he];exact hb) ht
    have hs : store [] (out++[low a b]++(scan xs (borrow a b)).1) (scan xs (borrow a b)).2=
        store [] (out++(scan (a::xs) b).1) (scan (a::xs) b).2 := by simp [scan,List.append_assoc]
    rw [hs] at H
    convert H using 1 <;> first | rfl | simp;omega

lemma scan_length (xs : List Bool) (b : Bool) : (scan xs b).1.length=xs.length := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simpa only [scan,List.length_cons] using congrArg Nat.succ (ih (borrow a b))
lemma program_run (xs : List Bool) (b : Bool) :
    Run program (store xs [] b) (6*xs.length+2) (store (scan xs b).1 [] (scan xs b).2) := by
  have h1 := pass_run xs [] b
  simp only [List.nil_append] at h1
  have h2 := move_run (1:K) 0 (by decide) (store [] (scan xs b).1 (scan xs b).2)
  have he2 : Function.update (Function.update (store [] (scan xs b).1 (scan xs b).2) 1 []) 0
      (store [] (scan xs b).1 (scan xs b).2 0++(store [] (scan xs b).1 (scan xs b).2 1).reverse)=
      store (scan xs b).1 [] (scan xs b).2 := by
    funext k;fin_cases k <;> simp [store]
  rw [he2] at h2
  have hl : (store [] (scan xs b).1 (scan xs b).2 1).length=xs.length := scan_length xs b
  rw [hl] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

lemma scan_equation (xs : List Bool) (b : Bool) :
    Add.value xs+2^xs.length*Add.bit (scan xs b).2=Add.value (scan xs b).1+Add.bit b := by
  induction xs generalizing b with
  | nil => simp [scan,Add.value]
  | cons a xs ih =>
    have hi := ih (borrow a b)
    have hb := bit_equation a b
    simp only [scan,List.length_cons,Add.value,Nat.pow_succ]
    nlinarith
lemma scan_borrow (xs : List Bool) : (scan xs true).2=true ↔ Add.value xs=0 := by
  have hh := scan_equation xs true
  have hz := Add.value_lt (scan xs true).1
  rw [scan_length] at hz
  have hx := Add.value_lt xs
  cases hb : (scan xs true).2 <;> simp [hb,Add.bit] at hh <;> simp <;> omega
lemma scan_value (xs : List Bool) (hx : 0<Add.value xs) :
    Add.value (scan xs true).1=Add.value xs-1 := by
  have hb : (scan xs true).2=false := by
    cases h : (scan xs true).2
    · rfl
    · have hh := (scan_borrow xs).mp h;omega
  have hh := scan_equation xs true
  simp only [hb,Add.bit,Bool.false_eq_true,↓reduceIte,Nat.mul_zero,Nat.add_zero] at hh
  omega

end SourceBurnside.Structured.Binary.Decrement

namespace SourceBurnside.Structured.Device
open Program Binary
variable {ι : Type} [DecidableEq ι]

lemma last_value (w : List Bool) (hw : w≠[]) (hv : Add.value w.reverse≤1) :
    ∃v b,w=v++[b] ∧ Add.value w.reverse=Add.bit b := by
  induction w using List.reverseRecOn with
  | nil => exact False.elim (hw rfl)
  | append_singleton v b ih =>
    refine ⟨v,b,rfl,?_⟩
    cases b <;> simp [List.reverse_append,Add.value,Add.bit] at * <;> omega

namespace Branch
variable {f g h : (ι → ℕ) → ℕ} {P Q S : ℕ → (ι → ℕ) → Prop}
variable (C : Realizer f P) (A : Realizer g Q) (B : Realizer h S)
abbrev Work := C.W ⊕ (A.W ⊕ (B.W ⊕ Unit))
abbrev L := ι ⊕ Work C A B

def flag : L C A B := .inr (.inl C.out)
def out : L C A B := .inr (.inr (.inr (.inr ())))
def cond : ι ⊕ C.W → L C A B := Sum.map id Sum.inl
def yes : ι ⊕ A.W → L C A B
  | .inl i => .inl i
  | .inr w => if w=A.out then out C A B else .inr (.inr (.inl w))
def no : ι ⊕ B.W → L C A B
  | .inl i => .inl i
  | .inr w => if w=B.out then out C A B else .inr (.inr (.inr (.inl w)))
lemma cond_injective : Function.Injective (cond C A B) := by
  intro firstValue secondValue equality
  cases firstValue <;> cases secondValue <;> simp_all [cond]
lemma yes_injective : Function.Injective (yes C A B) := by
  intro x y hh;cases x with
  | inl i => cases y with
    | inl j => simpa [yes] using hh
    | inr w => by_cases hw : w=A.out <;> simp_all [yes,out]
  | inr v => cases y with
    | inl i => by_cases hv : v=A.out <;> simp_all [yes,out]
    | inr w => by_cases hv : v=A.out <;> by_cases hw : w=A.out <;> simp_all [yes,out]
lemma no_injective : Function.Injective (no C A B) := by
  intro x y hh;cases x with
  | inl i => cases y with
    | inl j => simpa [no] using hh
    | inr w => by_cases hw : w=B.out <;> simp_all [no,out]
  | inr v => cases y with
    | inl i => by_cases hv : v=B.out <;> simp_all [no,out]
    | inr w => by_cases hv : v=B.out <;> by_cases hw : w=B.out <;> simp_all [no,out]

def body (b : Bool) : Program (L C A B) := .seq
  (if b then A.program.relabel (yes C A B) else B.program.relabel (no C A B)) (clear (flag C A B))
def program : Program (L C A B) := .seq (C.program.relabel (cond C A B))
  (.pop (flag C A B) (fun b => body C A B (b.getD false)))
def pending (xs : ι → List Bool) (v : List Bool) : Store (L C A B) := Function.update (input xs) (flag C A B) v

lemma finish_run (xs : ι → List Bool) (v y : List Bool) :
    Run (clear (flag C A B)) (Function.update (pending C A B xs v) (out C A B) y) (2*v.length+1)
      (Function.update (input xs) (out C A B) y) := by
  have h := clear_run (flag C A B) (Function.update (pending C A B xs v) (out C A B) y)
  have hl : (Function.update (pending C A B xs v) (out C A B) y) (flag C A B)=v := by simp [pending,flag,out]
  rw [hl] at h
  have he : Function.update (Function.update (pending C A B xs v) (out C A B) y) (flag C A B) []=
      Function.update (input xs) (out C A B) y := by
    funext k
    by_cases hk : k=flag C A B
    · subst k;simp [flag,out,input]
    · by_cases ho : k=out C A B
      · subst k
        have hfo : out C A B≠flag C A B := by simp [flag,out]
        simp only [Function.update_of_ne hfo,Function.update_self]
      · simp only [pending,Function.update_of_ne hk,Function.update_of_ne ho]
  rwa [he] at h

lemma branch_call {j : (ι → ℕ) → ℕ} {Ad : ℕ → (ι → ℕ) → Prop} (D : Realizer j Ad)
    (e : ι ⊕ D.W → L C A B) (he : Function.Injective e) (ho : e (.inr D.out)=out C A B)
    (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n) (hp : Ad n (values xs))
    (v : List Bool) (hinit : ∀i,pending C A B xs v (e (.inl i))=xs i)
    (hwork : ∀w,pending C A B xs v (e (.inr w))=[]) :
    ∃t y,t≤D.coefficient*(n+1)^2+2*v.length+1 ∧ y.length=n ∧ Add.value y.reverse=j (values xs) ∧
      Run (.seq (D.program.relabel e) (clear (flag C A B))) (pending C A B xs v) t
        (Function.update (input xs) (out C A B) y) := by
  obtain ⟨t,y,ht,hy,hval,hRun⟩ := D.transport e he n hn xs hxs hp (pending C A B xs v) hinit hwork
  rw [ho] at hRun
  have hclear := finish_run C A B xs v y
  exact ⟨t+(2*v.length+1),y,by omega,hy,hval,Run.seq _ _ _ _ _ _ _ hRun hclear⟩

lemma body_run (b : Bool) (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n)
    (v : List Bool) (hp : if b then Q n (values xs) else S n (values xs)) :
    ∃t y,t≤(A.coefficient+B.coefficient)*(n+1)^2+2*v.length+1 ∧ y.length=n ∧
      Add.value y.reverse=(if b then g (values xs) else h (values xs)) ∧
      Run (body C A B b) (pending C A B xs v) t (Function.update (input xs) (out C A B) y) := by
  cases b
  · obtain ⟨t,y,ht,hy,hv,hR⟩ := branch_call C A B B (no C A B) (no_injective C A B)
      (by simp [no]) n hn xs hxs hp v
      (by intro i;simp [pending,no,flag,input,-Sum.update_elim_inr,-Sum.elim_update_right])
      (by intro w;by_cases hw : w=B.out <;> simp [pending,no,flag,out,input,hw,-Sum.update_elim_inr,-Sum.elim_update_right])
    exact ⟨t,y,by nlinarith,hy,hv,hR⟩
  · obtain ⟨t,y,ht,hy,hv,hR⟩ := branch_call C A B A (yes C A B) (yes_injective C A B)
      (by simp [yes]) n hn xs hxs hp v
      (by intro i;simp [pending,yes,flag,input,-Sum.update_elim_inr,-Sum.elim_update_right])
      (by intro w;by_cases hw : w=A.out <;> simp [pending,yes,flag,out,input,hw,-Sum.update_elim_inr,-Sum.elim_update_right])
    exact ⟨t,y,by nlinarith,hy,hv,hR⟩

lemma program_run (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n)
    (hP : P n (values xs)) (hf : f (values xs)≤1)
    (hp : if f (values xs)=0 then S n (values xs) else Q n (values xs)) :
    ∃t y,t≤(C.coefficient+A.coefficient+B.coefficient+4)*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=(if f (values xs)=0 then h (values xs) else g (values xs)) ∧
      Run (program C A B) (input xs) t (Function.update (input xs) (out C A B) y) := by
  obtain ⟨tc,yc,htc,hyc,hvc,hc⟩ := C.transport (cond C A B) (cond_injective C A B) n hn xs hxs hP
    (input xs) (by intro i;rfl) (by intro w;rfl)
  have hc' : Run (C.program.relabel (cond C A B)) (input xs) tc (pending C A B xs yc) := hc
  have hyn : yc≠[] := by intro he;rw [he] at hyc;simp at hyc;omega
  obtain ⟨v,b,hvb,hval⟩ := last_value yc hyn (hvc ▸ hf)
  have hb : f (values xs)=Add.bit b := hvc.symm.trans hval
  have had : if b then Q n (values xs) else S n (values xs) := by cases b <;> simpa [hb,Add.bit] using hp
  obtain ⟨tb,y,htb,hy,hyv,hr⟩ := body_run C A B b n hn xs hxs v had
  have pp : pending C A B xs yc (flag C A B)=v++[b] := by simp [pending,hvb]
  have pu : Function.update (pending C A B xs yc) (flag C A B) v=pending C A B xs v := by simp [pending]
  have hpop : Run (.pop (flag C A B) (fun bb => body C A B (bb.getD false)))
      (pending C A B xs yc) (1+tb) (Function.update (input xs) (out C A B) y) := by
    refine Run.pop _ _ _ _ _ ?_
    simpa only [pp,List.getLast?_concat,List.dropLast_concat,Option.getD_some,pu] using hr
  have H := Run.seq _ _ _ _ _ _ _ hc' hpop
  refine ⟨tc+(1+tb),y,?_,hy,?_,H⟩
  · have hvlen : v.length+1=n := by rw [hvb,List.length_append,List.length_singleton] at hyc;exact hyc
    nlinarith
  · cases b <;> simpa [hb,Add.bit] using hyv

def realizer : Realizer (fun vs => if f vs=0 then h vs else g vs)
    (fun n vs => P n vs ∧ f vs≤1 ∧ (if f vs=0 then S n vs else Q n vs)) where
  W := Work C A B
  finiteW := inferInstance
  eqW := inferInstance
  out := .inr (.inr (.inr ()))
  program := program C A B
  coefficient := C.coefficient+A.coefficient+B.coefficient+4
  spec := by
    intro n hn xs hs hp
    exact program_run C A B n hn xs hs hp.1 hp.2.1 hp.2.2
end Branch
end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Binary.Power
open Program
abbrev K := Fin 6

def store (cnt acc ys : List Bool) : Store K := ![cnt.reverse,acc.reverse,[],[],[],ys.reverse]
def trial (cnt acc ys : List Bool) (b : List Bool) : Store K := ![cnt.reverse,acc.reverse,[],b,[],ys.reverse]
def regs : Fin 3 → K := ![0,2,3]
lemma regs_injective : Function.Injective regs := by decide

def finish (b : Bool) : Program K := if b then mapInPlace (fun _ => false) 0 4 else shift 1 4
def step : Program K := .seq (.push 3 true) (.seq (Decrement.program.relabel regs)
  (.pop 3 (fun b => finish (b.getD false))))
def program : Program K := .loop 5 (fun _ => step)
def oneStep (cnt acc : List Bool) : List Bool × List Bool :=
  let t := Decrement.scan cnt true
  if t.2 then (List.replicate cnt.length false,acc) else (t.1,Add.double acc)

def iter : ℕ → List Bool → List Bool → List Bool × List Bool
  | 0,cnt,acc => (cnt,acc)
  | m+1,cnt,acc => let t := oneStep cnt acc; iter m t.1 t.2

lemma finish_run (cnt acc ys : List Bool) (b : Bool) (hlen : cnt.length=acc.length) (ha : acc≠[]) :
    Run (finish b) (store cnt acc ys) (4*cnt.length+2)
      (store (if b then List.replicate cnt.length false else cnt) (if b then acc else Add.double acc) ys) := by
  cases b
  · have H := shift_run (1:K) 4 (by decide) (store cnt acc ys) (by rfl) (by simpa [store] using ha)
    have he : Function.update (store cnt acc ys) 1 ((store cnt acc ys 1).tail++[false])=store cnt (Add.double acc) ys := by
      funext k;fin_cases k <;> simp [store,Add.double_reverse]
    rw [he] at H
    have hl : (store cnt acc ys 1).length=cnt.length := by simp [store,hlen]
    rw [hl] at H
    exact H
  · have H := mapInPlace_run (fun _ => false) (0:K) 4 (by decide) (store cnt acc ys) (by rfl)
    have he : Function.update (store cnt acc ys) 0 ((store cnt acc ys 0).map (fun _ => false))=
        store (List.replicate cnt.length false) acc ys := by
      funext k;fin_cases k <;> simp [store]
    rw [he] at H
    simpa [store,finish] using H

lemma step_run (cnt acc ys : List Bool) (hlen : cnt.length=acc.length) (ha : acc≠[]) :
    Run step (store cnt acc ys) (10*cnt.length+6) (store (oneStep cnt acc).1 (oneStep cnt acc).2 ys) := by
  have h1 := Run.push (store cnt acc ys) (3:K) true
  have he1 : Function.update (store cnt acc ys) 3 ((store cnt acc ys 3)++[true])=trial cnt acc ys [true] := by
    funext k;fin_cases k <;> simp [store,trial]
  rw [he1] at h1
  let dc := Decrement.scan cnt true
  have h2 : Run (Decrement.program.relabel regs) (trial cnt acc ys [true]) (6*cnt.length+2)
      (trial dc.1 acc ys [dc.2]) := by
    refine (Decrement.program_run cnt true).relabel_to regs regs_injective _ _ ?_ ?_ ?_
    · intro k;fin_cases k <;> rfl
    · intro k;fin_cases k <;> rfl
    · intro l hl;fin_cases l
      · exact False.elim (hl 0 rfl)
      · rfl
      · exact False.elim (hl 1 rfl)
      · exact False.elim (hl 2 rfl)
      · rfl
      · rfl
  have hdlen : dc.1.length=cnt.length := Decrement.scan_length cnt true
  have h3 : Run (.pop (3:K) (fun b => finish (b.getD false))) (trial dc.1 acc ys [dc.2])
      (1+(4*cnt.length+2)) (store (oneStep cnt acc).1 (oneStep cnt acc).2 ys) := by
    refine Run.pop _ _ _ _ _ ?_
    have hc : trial dc.1 acc ys [dc.2] 3=[dc.2] := rfl
    have he : Function.update (trial dc.1 acc ys [dc.2]) 3 []=store dc.1 acc ys := by
      funext k;fin_cases k <;> simp [trial,store]
    simp only [hc,List.getLast?_singleton,Option.getD_some,List.dropLast_singleton,he]
    have H := finish_run dc.1 acc ys dc.2 (hdlen.trans hlen) ha
    rw [hdlen] at H
    cases hb : dc.2 <;> simpa [oneStep,dc,hb] using H
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

lemma oneStep_lengths (cnt acc : List Bool) (ha : acc≠[]) :
    (oneStep cnt acc).1.length=cnt.length ∧ (oneStep cnt acc).2.length=acc.length := by
  dsimp only [oneStep]
  split
  · simp
  · simp [Decrement.scan_length,Add.double_length acc ha]

lemma iter_lengths (m : ℕ) (cnt acc : List Bool) (ha : acc≠[]) :
    (iter m cnt acc).1.length=cnt.length ∧ (iter m cnt acc).2.length=acc.length := by
  induction m generalizing cnt acc with
  | zero => exact ⟨rfl,rfl⟩
  | succ m ih =>
    have h := oneStep_lengths cnt acc ha
    have hn : (oneStep cnt acc).2≠[] := by intro he;have hp := List.length_pos_iff.mpr ha;rw [he] at h;simp at h;omega
    have hh := ih (oneStep cnt acc).1 (oneStep cnt acc).2 hn
    exact ⟨hh.1.trans h.1,hh.2.trans h.2⟩

lemma program_run (cnt acc ys : List Bool) (hlen : cnt.length=acc.length) (ha : acc≠[]) :
    Run program (store cnt acc ys) ((10*cnt.length+7)*ys.length+1)
      (store (iter ys.length cnt acc).1 (iter ys.length cnt acc).2 []) := by
  induction ys generalizing cnt acc with
  | nil => exact Run.loop_nil (store cnt acc []) (5:K) (fun _ => step) (by rfl)
  | cons b ys ih =>
    have hh := oneStep_lengths cnt acc ha
    have hn : (oneStep cnt acc).2≠[] := by intro he;have hp := List.length_pos_iff.mpr ha;rw [he] at hh;simp at hh;omega
    have hlen' : (oneStep cnt acc).1.length=(oneStep cnt acc).2.length := by omega
    have ht := ih (oneStep cnt acc).1 (oneStep cnt acc).2 hlen' hn
    rw [hh.1] at ht
    have he : Function.update (store cnt acc (b::ys)) 5 ys.reverse=store cnt acc ys := by
      funext k;fin_cases k <;> simp [store]
    have hs := step_run cnt acc ys hlen ha
    have H := Run.loop_cons (store cnt acc (b::ys)) (5:K) (fun _ => step) ys.reverse b _ _ _ _
      (by simp [store]) (by rw [he];exact hs) ht
    convert H using 1 <;> first | rfl | simp;ring

lemma oneStep_counter (cnt acc : List Bool) : Add.value (oneStep cnt acc).1=Add.value cnt-1 := by
  by_cases hz : Add.value cnt=0
  · have hb := (Decrement.scan_borrow cnt).mpr hz
    simp [oneStep,hb,Divide.zero_value,hz]
  · have hb : (Decrement.scan cnt true).2=false := Bool.eq_false_iff.mpr (by intro h;exact hz ((Decrement.scan_borrow cnt).mp h))
    simpa [oneStep,hb] using Decrement.scan_value cnt (by omega)

lemma oneStep_value (cnt acc : List Bool) (ha : acc≠[]) :
    Add.value (oneStep cnt acc).2=
      if Add.value cnt=0 then Add.value acc else (2*Add.value acc)%2^acc.length := by
  by_cases hz : Add.value cnt=0
  · have hb := (Decrement.scan_borrow cnt).mpr hz
    simp [oneStep,hb,hz]
  · have hb : (Decrement.scan cnt true).2=false := Bool.eq_false_iff.mpr (by intro h;exact hz ((Decrement.scan_borrow cnt).mp h))
    simp [oneStep,hb,hz,Add.double_value acc ha]

lemma iter_counter (m : ℕ) (cnt acc : List Bool) : Add.value (iter m cnt acc).1=Add.value cnt-m := by
  induction m generalizing cnt acc with
  | zero => simp [iter]
  | succ m ih => simp [iter,ih,oneStep_counter,Nat.sub_sub,Nat.add_comm]

lemma iter_value (m : ℕ) (cnt acc : List Bool) (ha : acc≠[]) :
    Add.value (iter m cnt acc).2=(Add.value acc*2^(min m (Add.value cnt)))%2^acc.length := by
  induction m generalizing cnt acc with
  | zero => simpa [iter] using (Nat.mod_eq_of_lt (Add.value_lt acc)).symm
  | succ m ih =>
    have hl := oneStep_lengths cnt acc ha
    have hn : (oneStep cnt acc).2≠[] := by intro he;have hp := List.length_pos_iff.mpr ha;rw [he] at hl;simp at hl;omega
    have H := ih (oneStep cnt acc).1 (oneStep cnt acc).2 hn
    change Add.value (iter m (oneStep cnt acc).1 (oneStep cnt acc).2).2=_
    rw [H,oneStep_counter,oneStep_value cnt acc ha,hl.2]
    by_cases hz : Add.value cnt=0
    · simp [hz]
    · have hm : min (m+1) (Add.value cnt)=min m (Add.value cnt-1)+1 := by omega
      rw [ite_eq_right hz,hm,Nat.pow_succ]
      rw [Nat.mod_mul_mod]
      congr 1
      ring
end SourceBurnside.Structured.Binary.Power

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type} [DecidableEq K]
def one (src tmp : K) : Program K := .seq (mapInPlace (fun _ => false) src tmp) (.pop src (fun _ => .push src true))
lemma one_run (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[]) :
    Run (one src tmp) r (4*(r src).length+4)
      (Function.update r src (Device.CompareOperator.padded (r src).length true)) := by
  let s := Function.update r src (List.replicate (r src).length false)
  have h1 := mapInPlace_run (fun _ => false) src tmp hne r ht
  have he1 : Function.update r src ((r src).map (fun _ => false))=s := by simp [s]
  rw [he1] at h1
  let t := Function.update r src (List.replicate ((r src).length-1) false)
  have h2 : Run (.pop src (fun _ => Program.push src true)) s 2
      (Function.update r src (Device.CompareOperator.padded (r src).length true)) := by
    refine Run.pop s src _ 1 _ ?_
    have h3 := Run.push t src true
    simpa [t,s,Device.CompareOperator.padded,List.dropLast_replicate] using h3
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1
  rfl
end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Device
open Program Binary
namespace PowerOperator
abbrev L := Fin 1 ⊕ Fin 6

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 4))
  (.seq (copy (.inl 0) (.inr 1) (.inr 4))
  (.seq (one (.inr 1) (.inr 4)) (copy (.inl 0) (.inr 5) (.inr 4))))
def program : Program L := .seq load (.seq (Power.program.relabel Sum.inr) (clear (.inr 0)))
def loaded (xs : Fin 1 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (Power.store (xs 0).reverse (CompareOperator.padded n true).reverse (xs 0).reverse)

lemma load_run (xs : Fin 1 → List Bool) (n : ℕ) (hs : (xs 0).length=n) :
    Run load (input xs) (19*n+10) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 6)) (xs 0)
  let R2 := Function.update R1 (.inr (1:Fin 6)) (xs 0)
  let R3 := Function.update R1 (.inr (1:Fin 6)) (CompareOperator.padded n true)
  have h1 := copy_run (.inl (0:Fin 1)) (.inr (0:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R (by rfl)
  change Run (copy (.inl (0:Fin 1)) (.inr (0:Fin 6)) (.inr 4)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := copy_run (.inl (0:Fin 1)) (.inr (1:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 1) (R1 (.inr 1)++R1 (.inl 0))=R2 := by
    simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : (R1 (.inl 0)).length=n := by simp [R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := one_run (.inr (1:Fin 6)) (.inr 4) (by simp) R2
    (by simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have hl3 : (R2 (.inr 1)).length=n := by simp [R2,hs]
  rw [hl3] at h3
  have he3 : Function.update R2 (.inr 1) (CompareOperator.padded n true)=R3 := by simp [R3,R2]
  rw [he3] at h3
  have h4 := copy_run (.inl (0:Fin 1)) (.inr (5:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R3
    (by simp [R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 5) (R3 (.inr 5)++R3 (.inl 0))=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,Power.store,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 0)).length=n := by simp [R3,R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

lemma program_correct (xs : Fin 1 → List Bool) (n : ℕ) (hn : 0<n) (hs : (xs 0).length=n)
    (hsmall : values xs 0<n) :
    ∃t y,t≤50*(n+1)^2 ∧ y.length=n ∧ Add.value y.reverse=2^(values xs 0) ∧
      Run program (input xs) t (result xs (1:Fin 6) y) := by
  let cnt := (xs 0).reverse
  let acc := (CompareOperator.padded n true).reverse
  let ys := (xs 0).reverse
  let qr := Power.iter ys.length cnt acc
  have hcnt : cnt.length=n := by simp [cnt,hs]
  have hacc : acc.length=n := by simpa [acc] using CompareOperator.padded_length n hn true
  have hav : Add.value acc=1 := by simp [acc,CompareOperator.padded_value,Add.bit]
  have ha : acc≠[] := by intro h;rw [h] at hacc;simp at hacc;omega
  have hy : ys.length=n := by simp [ys,hs]
  have hl := Power.iter_lengths ys.length cnt acc ha
  have hc' : qr.1.length=n := hl.1.trans hcnt
  have ha' : qr.2.length=n := hl.2.trans hacc
  let R : Store L := Sum.elim xs (Power.store qr.1 qr.2 [])
  have H1 := load_run xs n hs
  have H2 : Run (Power.program.relabel Sum.inr) (loaded xs n) ((10*n+7)*n+1) R := by
    have H := (Power.program_run cnt acc ys (hcnt.trans hacc.symm) ha).relabel_to Sum.inr Sum.inr_injective
      (loaded xs n) R (by intro k;rfl) (by intro k;rfl) (by
        intro l hl;cases l with
        | inl i => rfl
        | inr k => exact False.elim (hl k rfl))
    simpa [hcnt,hy] using H
  have H3 := clear_run (.inr (0:Fin 6)) R
  have hl3 : (R (.inr 0)).length=n := by simp only [R,Sum.elim_inr,Power.store,Matrix.cons_val_zero,List.length_reverse];exact hc'
  rw [hl3] at H3
  have he3 : Function.update R (.inr 0) []=result xs (1:Fin 6) qr.2.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Power.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at H3
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 H3)
  refine ⟨(10*n+7)*n+21*n+12,qr.2.reverse,by nlinarith,by simpa using ha',?_,?_⟩
  · simp only [List.reverse_reverse]
    have hv := Power.iter_value ys.length cnt acc ha
    rw [hy,hacc,hav,Nat.one_mul] at hv
    change Add.value (Power.iter n cnt acc).2 = 2^min n (values xs 0)%2^n at hv
    rw [Nat.min_eq_right (Nat.le_of_lt hsmall)] at hv
    have hp : 2^(values xs 0)<2^n := Nat.pow_lt_pow_right (by decide) hsmall
    simpa [qr,hy] using hv.trans (Nat.mod_eq_of_lt hp)
  · convert H using 1 <;> first | rfl | omega
end PowerOperator

def powerTwo : Realizer (fun vs : Fin 1 → ℕ => 2^(vs 0)) (fun n vs => vs 0<n) where
  W := Fin 6
  finiteW := inferInstance
  eqW := inferInstance
  out := 1
  program := PowerOperator.program
  coefficient := 50
  spec := by
    intro n hn xs hs hp
    exact PowerOperator.program_correct xs n hn (hs 0) hp
end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Device
open Program Binary
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable {f : (ι → ℕ) → ℕ} {P : ℕ → (ι → ℕ) → Prop}

def Realizer.weaken (D : Realizer f P) (Q : ℕ → (ι → ℕ) → Prop)
    (h : ∀n vs,Q n vs → P n vs) : Realizer f Q where
  W := D.W
  finiteW := D.finiteW
  eqW := D.eqW
  out := D.out
  program := D.program
  coefficient := D.coefficient
  spec := by intro n hn xs hs hp;exact D.spec n hn xs hs (h n (values xs) hp)

def Realizer.reinput (D : Realizer f P) (e : ι → κ) (he : Function.Injective e) :
    Realizer (fun vs => f (vs ∘ e)) (fun n vs => P n (vs ∘ e)) where
  W := D.W
  finiteW := D.finiteW
  eqW := D.eqW
  out := D.out
  program := D.program.relabel (Sum.map e id)
  coefficient := D.coefficient
  spec := by
    intro n hn xs hs hp
    have he' : Function.Injective (Sum.map e (id:D.W → D.W)) := by
      intro x y hxy;cases x <;> cases y
      · exact congrArg Sum.inl (he (by simpa using hxy))
      · simp at hxy
      · simp at hxy
      · simpa using hxy
    have H := D.transport (Sum.map e id) he' n hn (xs ∘ e) (by intro i;exact hs (e i)) hp
      (input xs) (by intro i;rfl) (by intro w;rfl)
    exact H

def composeUnary {g : (Fin 1 → ℕ) → ℕ} {Q : ℕ → (Fin 1 → ℕ) → Prop}
    (D : Realizer f P) (O : Realizer g Q) :
    Realizer (fun vs => g (fun _ => f vs)) (fun n vs => P n vs ∧ Q n (fun _ => f vs)) := by
  let e : Fin 1 → Fin 2 := fun _ => 0
  let O' := O.reinput e (by intro i j h;exact Subsingleton.elim i j)
  have hh := Compose.realizer (op:=fun a _ => g (fun _ => a)) D D O'
  exact hh.weaken _ (by intro n vs h;exact ⟨h.1,h.1,h.2⟩)

end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Binary.Increment
open Program
abbrev K := Fin 3

def store (xs out : List Bool) (b : Bool) : Store K := ![xs.reverse,out,[b]]
def partialStore (xs out : List Bool) : Store K := ![xs.reverse,out,[]]
def low (a b : Bool) := a ^^ b
def carry (a b : Bool) := a && b
lemma bit_equation (a b : Bool) : Add.bit a+Add.bit b=Add.bit (low a b)+2*Add.bit (carry a b) := by
  cases a <;> cases b <;> decide

def step (a : Bool) : Program K := .pop 2 (fun b =>
  .seq (.push 1 (low a (b.getD false))) (.push 2 (carry a (b.getD false))))
def pass : Program K := .loop 0 step
def program : Program K := .seq pass (move 1 0)
def scan : List Bool → Bool → List Bool × Bool
  | [],b => ([],b)
  | a::xs,b => let t := scan xs (carry a b); (low a b::t.1,t.2)

lemma step_run (xs out : List Bool) (a b : Bool) :
    Run (step a) (store xs out b) 3 (store xs (out++[low a b]) (carry a b)) := by
  have h1 := Run.push (partialStore xs out) (1:K) (low a b)
  let t := Function.update (partialStore xs out) 1 (out++[low a b])
  have hx : Run (.push (1:K) (low a b)) (partialStore xs out) 1 t := by simpa [partialStore,t] using h1
  have h2 := Run.push t (2:K) (carry a b)
  have he2 : Function.update t 2 (t 2++[carry a b])=store xs (out++[low a b]) (carry a b) := by
    funext k;fin_cases k <;> simp [t,partialStore,store]
  rw [he2] at h2
  have hs := Run.seq _ _ _ _ _ _ _ hx h2
  unfold step
  refine Run.pop (store xs out b) (2:K) _ 2 _ ?_
  change Run (.seq (.push 1 (low a b)) (.push 2 (carry a b)))
    (Function.update (store xs out b) 2 []) 2 _
  have he : Function.update (store xs out b) 2 []=partialStore xs out := by funext k;fin_cases k <;> simp [store,partialStore]
  rw [he];exact hs

lemma pass_run (xs out : List Bool) (b : Bool) :
    Run pass (store xs out b) (4*xs.length+1) (store [] (out++(scan xs b).1) (scan xs b).2) := by
  induction xs generalizing out b with
  | nil => simpa [pass,scan] using Run.loop_nil (store [] out b) (0:K) step (by rfl)
  | cons a xs ih =>
    have he : Function.update (store (a::xs) out b) 0 xs.reverse=store xs out b := by
      funext k;fin_cases k <;> simp [store]
    have hb := step_run xs out a b
    have ht := ih (out++[low a b]) (carry a b)
    have H := Run.loop_cons (store (a::xs) out b) (0:K) step xs.reverse a _ _ 3 (4*xs.length+1)
      (by simp [store]) (by rw [he];exact hb) ht
    have hs : store [] (out++[low a b]++(scan xs (carry a b)).1) (scan xs (carry a b)).2=
        store [] (out++(scan (a::xs) b).1) (scan (a::xs) b).2 := by simp [scan,List.append_assoc]
    rw [hs] at H
    convert H using 1 <;> first | rfl | simp;omega

lemma scan_length (xs : List Bool) (b : Bool) : (scan xs b).1.length=xs.length := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simpa only [scan,List.length_cons] using congrArg Nat.succ (ih (carry a b))
lemma program_run (xs : List Bool) (b : Bool) :
    Run program (store xs [] b) (6*xs.length+2) (store (scan xs b).1 [] (scan xs b).2) := by
  have h1 := pass_run xs [] b
  simp only [List.nil_append] at h1
  have h2 := move_run (1:K) 0 (by decide) (store [] (scan xs b).1 (scan xs b).2)
  have he2 : Function.update (Function.update (store [] (scan xs b).1 (scan xs b).2) 1 []) 0
      (store [] (scan xs b).1 (scan xs b).2 0++(store [] (scan xs b).1 (scan xs b).2 1).reverse)=
      store (scan xs b).1 [] (scan xs b).2 := by
    funext k;fin_cases k <;> simp [store]
  rw [he2] at h2
  have hl : (store [] (scan xs b).1 (scan xs b).2 1).length=xs.length := scan_length xs b
  rw [hl] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

lemma scan_equation (xs : List Bool) (b : Bool) :
    Add.value xs+Add.bit b=Add.value (scan xs b).1+2^xs.length*Add.bit (scan xs b).2 := by
  induction xs generalizing b with
  | nil => simp [scan,Add.value]
  | cons a xs ih =>
    have hi := ih (carry a b)
    have hb := bit_equation a b
    simp only [scan,List.length_cons,Add.value,Nat.pow_succ]
    nlinarith
lemma scan_value (xs : List Bool) (hx : Add.value xs+1<2^xs.length) :
    Add.value (scan xs true).1=Add.value xs+1 := by
  have hh := scan_equation xs true
  have hb : (scan xs true).2=false := by
    cases h : (scan xs true).2
    · rfl
    · simp [h,Add.bit] at hh;omega
  simp [hb,Add.bit] at hh
  omega
end SourceBurnside.Structured.Binary.Increment

namespace SourceBurnside.Structured.Binary.BitSize
open Program
abbrev K := Fin 5

def store (xs cnt len : List Bool) : Store K := ![xs.reverse,cnt.reverse,len.reverse,[],[]]
def trial (xs cnt len : List Bool) (flag : List Bool) : Store K := ![xs.reverse,cnt.reverse,len.reverse,[],flag]
def regs : Fin 3 → K := ![1,3,4]
lemma regs_injective : Function.Injective regs := by decide

def finish (a : Bool) : Program K := if a then .seq (clear 2) (copy 1 2 3) else .skip
def step (a : Bool) : Program K := .seq (.push 4 true) (.seq (Increment.program.relabel regs)
  (.pop 4 (fun _ => finish a)))
def program : Program K := .loop 0 step

def oneStep (a : Bool) (cnt len : List Bool) : List Bool × List Bool :=
  let c := (Increment.scan cnt true).1
  (c,if a then c else len)
def iter : List Bool → List Bool → List Bool → List Bool × List Bool
  | [],cnt,len => (cnt,len)
  | a::xs,cnt,len => let t := oneStep a cnt len;iter xs t.1 t.2

def measure : List Bool → ℕ → ℕ → ℕ
  | [],_,r => r
  | a::xs,p,r => measure xs (p+1) (if a then p+1 else r)

lemma finish_run (a : Bool) (xs cnt len : List Bool) (h : cnt.length=len.length) :
    ∃t,t≤7*cnt.length+3 ∧ Run (finish a) (store xs cnt len) t (store xs cnt (if a then cnt else len)) := by
  cases a
  · exact ⟨1,by omega,Run.skip _⟩
  · let R := store xs cnt len
    let S := Function.update R (2:K) []
    have h1 := clear_run (2:K) R
    have hl : (R 2).length=cnt.length := by simp [R,store,h]
    rw [hl] at h1
    have h2 := copy_run (1:K) 2 3 (by decide) (by decide) (by decide) S (by simp [S,R,store])
    have he : Function.update S 2 (S 2++S 1)=store xs cnt cnt := by
      funext k;fin_cases k <;> simp [S,R,store]
    rw [he] at h2
    have hl2 : (S 1).length=cnt.length := by simp [S,R,store]
    rw [hl2] at h2
    refine ⟨7*cnt.length+3,le_rfl,?_⟩
    have H := Run.seq _ _ _ _ _ _ _ h1 h2
    convert H using 1 <;> first | rfl | omega

lemma step_run (a : Bool) (xs cnt len : List Bool) (h : cnt.length=len.length) :
    ∃t,t≤13*cnt.length+7 ∧ Run (step a) (store xs cnt len) t
      (store xs (oneStep a cnt len).1 (oneStep a cnt len).2) := by
  have h1 := Run.push (store xs cnt len) (4:K) true
  have he1 : Function.update (store xs cnt len) 4 ((store xs cnt len 4)++[true])=trial xs cnt len [true] := by
    funext k;fin_cases k <;> simp [store,trial]
  rw [he1] at h1
  let dc := Increment.scan cnt true
  have h2 : Run (Increment.program.relabel regs) (trial xs cnt len [true]) (6*cnt.length+2)
      (trial xs dc.1 len [dc.2]) := by
    refine (Increment.program_run cnt true).relabel_to regs regs_injective _ _ ?_ ?_ ?_
    · intro k;fin_cases k <;> rfl
    · intro k;fin_cases k <;> rfl
    · intro l hl;fin_cases l
      · rfl
      · exact False.elim (hl 0 rfl)
      · rfl
      · exact False.elim (hl 1 rfl)
      · exact False.elim (hl 2 rfl)
  have hdc : dc.1.length=cnt.length := Increment.scan_length cnt true
  obtain ⟨t,ht,h3⟩ := finish_run a xs dc.1 len (hdc.trans h)
  have h4 : Run (.pop (4:K) (fun _ => finish a)) (trial xs dc.1 len [dc.2]) (1+t)
      (store xs (oneStep a cnt len).1 (oneStep a cnt len).2) := by
    refine Run.pop _ _ _ _ _ ?_
    have hc : trial xs dc.1 len [dc.2] 4=[dc.2] := rfl
    have he : Function.update (trial xs dc.1 len [dc.2]) 4 []=store xs dc.1 len := by
      funext k;fin_cases k <;> simp [trial,store]
    simpa only [hc,List.getLast?_singleton,List.dropLast_singleton,he,oneStep] using h3
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h4)
  refine ⟨1+(6*cnt.length+2+(1+t)),by rw [hdc] at ht;omega,H⟩

lemma oneStep_lengths (a : Bool) (cnt len : List Bool) (h : cnt.length=len.length) :
    (oneStep a cnt len).1.length=cnt.length ∧ (oneStep a cnt len).2.length=len.length := by
  cases a <;> simp [oneStep,Increment.scan_length,h]
lemma iter_lengths (xs cnt len : List Bool) (h : cnt.length=len.length) :
    (iter xs cnt len).1.length=cnt.length ∧ (iter xs cnt len).2.length=len.length := by
  induction xs generalizing cnt len with
  | nil => exact ⟨rfl,rfl⟩
  | cons a xs ih =>
    have hh := oneStep_lengths a cnt len h
    have hi := ih (oneStep a cnt len).1 (oneStep a cnt len).2 (hh.1.trans (h.trans hh.2.symm))
    exact ⟨hi.1.trans hh.1,hi.2.trans hh.2⟩

lemma program_run (xs cnt len : List Bool) (h : cnt.length=len.length) :
    ∃t,t≤(13*cnt.length+8)*xs.length+1 ∧
      Run program (store xs cnt len) t (store [] (iter xs cnt len).1 (iter xs cnt len).2) := by
  induction xs generalizing cnt len with
  | nil => exact ⟨1,by simp,Run.loop_nil _ _ _ rfl⟩
  | cons a xs ih =>
    obtain ⟨t,ht,H⟩ := step_run a xs cnt len h
    have hh := oneStep_lengths a cnt len h
    obtain ⟨u,hu,U⟩ := ih (oneStep a cnt len).1 (oneStep a cnt len).2 (hh.1.trans (h.trans hh.2.symm))
    have he : Function.update (store (a::xs) cnt len) 0 xs.reverse=store xs cnt len := by
      funext k;fin_cases k <;> simp [store]
    refine ⟨1+t+u,?_,?_⟩
    · rw [hh.1] at hu;simp only [List.length_cons];nlinarith
    · have HH := Run.loop_cons (store (a::xs) cnt len) (0:K) step xs.reverse a _ _ t u (by simp [store]) (by rw [he];exact H) U
      convert HH using 1 <;> first | rfl | omega

lemma iter_value (xs cnt len : List Bool) (h : cnt.length=len.length)
    (hb : Add.value cnt+xs.length<2^cnt.length) :
    Add.value (iter xs cnt len).1=Add.value cnt+xs.length ∧
      Add.value (iter xs cnt len).2=measure xs (Add.value cnt) (Add.value len) := by
  induction xs generalizing cnt len with
  | nil => simp [iter,measure]
  | cons a xs ih =>
    have hc : Add.value cnt+1<2^cnt.length := by simp only [List.length_cons] at hb;omega
    have hv := Increment.scan_value cnt hc
    have hh := oneStep_lengths a cnt len h
    have hstep : Add.value (oneStep a cnt len).1=Add.value cnt+1 := hv
    have hlen : Add.value (oneStep a cnt len).2=if a then Add.value cnt+1 else Add.value len := by
      cases a <;> simp [oneStep,hv]
    have hi := ih (oneStep a cnt len).1 (oneStep a cnt len).2 (hh.1.trans (h.trans hh.2.symm))
      (by rw [hh.1,hstep];simp only [List.length_cons] at hb;omega)
    simpa [iter,measure,hstep,hlen,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi

lemma measure_value (xs : List Bool) (p r : ℕ) :
    measure xs p r=if Add.value xs=0 then r else p+(Add.value xs).size := by
  induction xs generalizing p r with
  | nil => simp [measure,Add.value]
  | cons a xs ih =>
    rw [measure,ih]
    have hb : Add.value (a::xs)=Nat.bit a (Add.value xs) := by
      cases a <;> simp [Add.value,Add.bit,Nat.bit]
      omega
    rw [hb]
    by_cases hz : Add.value xs=0
    · cases a <;> simp [hz,Nat.bit]
    · have hne : Nat.bit a (Add.value xs)≠0 := by
        cases a <;> simp [Nat.bit]
        omega
      simp [hz,hne,Nat.size_bit hne,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm]
end SourceBurnside.Structured.Binary.BitSize

namespace SourceBurnside.Structured.Device
open Program Binary
namespace SizeOperator
abbrev L := Fin 1 ⊕ Fin 5

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 3))
  (.seq (copy (.inl 0) (.inr 1) (.inr 3))
  (.seq (mapInPlace (fun _ => false) (.inr 1) (.inr 3))
  (.seq (copy (.inl 0) (.inr 2) (.inr 3)) (one (.inr 2) (.inr 3)))))
def program : Program L := .seq load (.seq (BitSize.program.relabel Sum.inr) (clear (.inr 1)))
def loaded (xs : Fin 1 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (BitSize.store (xs 0).reverse (List.replicate n false) (CompareOperator.padded n true).reverse)

lemma load_run (xs : Fin 1 → List Bool) (n : ℕ) (hs : (xs 0).length=n) :
    Run load (input xs) (23*n+12) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 5)) (xs 0)
  let R2 := Function.update R1 (.inr (1:Fin 5)) (xs 0)
  let R3 := Function.update R1 (.inr (1:Fin 5)) (List.replicate n false)
  let R4 := Function.update R3 (.inr (2:Fin 5)) (xs 0)
  have h1 := copy_run (.inl (0:Fin 1)) (.inr (0:Fin 5)) (.inr 3) (by simp) (by simp) (by simp) R rfl
  change Run (copy (.inl (0:Fin 1)) (.inr (0:Fin 5)) (.inr 3)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := copy_run (.inl (0:Fin 1)) (.inr (1:Fin 5)) (.inr 3) (by simp) (by simp) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 1) (R1 (.inr 1)++R1 (.inl 0))=R2 := by
    simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : (R1 (.inl 0)).length=n := by simp [R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := mapInPlace_run (fun _ => false) (.inr (1:Fin 5)) (.inr 3) (by simp) R2
    (by simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have hl3 : (R2 (.inr 1)).length=n := by simp [R2,hs]
  rw [hl3] at h3
  have he3 : Function.update R2 (.inr 1) ((R2 (.inr 1)).map (fun _ => false))=R3 := by simp [R3,R2,hs]
  rw [he3] at h3
  have h4 := copy_run (.inl (0:Fin 1)) (.inr (2:Fin 5)) (.inr 3) (by simp) (by simp) (by simp) R3
    (by simp [R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 2) (R3 (.inr 2)++R3 (.inl 0))=R4 := by
    simp [R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 0)).length=n := by simp [R3,R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have h5 := one_run (.inr (2:Fin 5)) (.inr 3) (by simp) R4
    (by simp [R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have hl5 : (R4 (.inr 2)).length=n := by simp [R4,hs]
  rw [hl5] at h5
  have he5 : Function.update R4 (.inr 2) (CompareOperator.padded n true)=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,BitSize.store,R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he5] at h5
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 (Run.seq _ _ _ _ _ _ _ h4 h5)))
  convert H using 1 <;> first | rfl | omega

lemma program_correct (xs : Fin 1 → List Bool) (n : ℕ) (hn : 0<n) (hs : (xs 0).length=n) :
    ∃t y,t≤60*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=(if values xs 0=0 then 1 else (values xs 0).size) ∧
      Run program (input xs) t (result xs (2:Fin 5) y) := by
  let ys := (xs 0).reverse
  let cnt := List.replicate n false
  let len := (CompareOperator.padded n true).reverse
  let qr := BitSize.iter ys cnt len
  have hy : ys.length=n := by simp [ys,hs]
  have hc : cnt.length=n := List.length_replicate
  have hl : len.length=n := by simpa [len] using CompareOperator.padded_length n hn true
  have hlen : cnt.length=len.length := hc.trans hl.symm
  have hcv : Add.value cnt=0 := Divide.zero_value n
  have hlv : Add.value len=1 := by simp [len,CompareOperator.padded_value,Add.bit]
  have hls := BitSize.iter_lengths ys cnt len hlen
  have hc' : qr.1.length=n := hls.1.trans hc
  have hl' : qr.2.length=n := hls.2.trans hl
  obtain ⟨t,ht,H2'⟩ := BitSize.program_run ys cnt len hlen
  let R : Store L := Sum.elim xs (BitSize.store [] qr.1 qr.2)
  have H2 : Run (BitSize.program.relabel Sum.inr) (loaded xs n) t R := by
    exact H2'.relabel_to Sum.inr Sum.inr_injective _ _ (by intro k;rfl) (by intro k;rfl)
      (by intro k hk;cases k with
          | inl i => rfl
          | inr j => exact False.elim (hk j rfl))
  have H1 := load_run xs n hs
  have H3 := clear_run (.inr (1:Fin 5)) R
  have hl3 : (R (.inr 1)).length=n := by simp only [R,Sum.elim_inr,BitSize.store,Matrix.cons_val_one,Matrix.cons_val_zero,List.length_reverse];exact hc'
  rw [hl3] at H3
  have he3 : Function.update R (.inr 1) []=result xs (2:Fin 5) qr.2.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,BitSize.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at H3
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 H3)
  refine ⟨23*n+12+(t+(2*n+1)),qr.2.reverse,?_,by simpa using hl',?_,H⟩
  · rw [hc,hy] at ht;nlinarith
  · simp only [List.reverse_reverse]
    have hv := (BitSize.iter_value ys cnt len hlen (by rw [hcv,hc,hy,Nat.zero_add];exact Nat.lt_two_pow_self)).2
    rw [BitSize.measure_value,hcv,hlv] at hv
    simp only [Nat.zero_add] at hv
    change Add.value qr.2=(if Add.value ys=0 then 1 else (Add.value ys).size)
    exact hv
end SizeOperator

def bitLength : Realizer (fun vs : Fin 1 → ℕ => if vs 0=0 then 1 else (vs 0).size) (fun _ _ => True) where
  W := Fin 5
  finiteW := inferInstance
  eqW := inferInstance
  out := 2
  program := SizeOperator.program
  coefficient := 60
  spec := by intro n hn xs hs hp;exact SizeOperator.program_correct xs n hn (hs 0)
end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Device

inductive Formula (ι : Type)
  | read : ι → Formula ι
  | constant : ℕ → Formula ι
  | add : Formula ι → Formula ι → Formula ι
  | sub : Formula ι → Formula ι → Formula ι
  | mul : Formula ι → Formula ι → Formula ι
  | div : Formula ι → Formula ι → Formula ι
  | mod : Formula ι → Formula ι → Formula ι
  | le : Formula ι → Formula ι → Formula ι
  | powTwo : Formula ι → Formula ι
  | bitLength : Formula ι → Formula ι
  | branch : Formula ι → Formula ι → Formula ι → Formula ι

namespace Formula
variable {ι : Type} [DecidableEq ι]
def eval : Formula ι → (ι → ℕ) → ℕ
  | .read i,vs => vs i
  | .constant a,_ => a
  | .add x y,vs => x.eval vs+y.eval vs
  | .sub x y,vs => x.eval vs-y.eval vs
  | .mul x y,vs => x.eval vs*y.eval vs
  | .div x y,vs => x.eval vs/y.eval vs
  | .mod x y,vs => x.eval vs%y.eval vs
  | .le x y,vs => if x.eval vs≤y.eval vs then 1 else 0
  | .powTwo x,vs => 2^(x.eval vs)
  | .bitLength x,vs => if x.eval vs=0 then 1 else (x.eval vs).size
  | .branch c a b,vs => if c.eval vs=0 then b.eval vs else a.eval vs

def Safe (n : ℕ) (vs : ι → ℕ) : Formula ι → Prop
  | .read _ => True
  | .constant a => a.bits.length≤n
  | .add x y => x.Safe n vs ∧ y.Safe n vs ∧ x.eval vs+y.eval vs<2^n
  | .sub x y => x.Safe n vs ∧ y.Safe n vs ∧ y.eval vs≤x.eval vs
  | .mul x y => x.Safe n vs ∧ y.Safe n vs ∧ x.eval vs*y.eval vs<2^n
  | .div x y | .mod x y => x.Safe n vs ∧ y.Safe n vs ∧ 0<y.eval vs ∧ 2*y.eval vs≤2^n
  | .le x y => x.Safe n vs ∧ y.Safe n vs
  | .powTwo x => x.Safe n vs ∧ x.eval vs<n
  | .bitLength x => x.Safe n vs
  | .branch c a b => c.Safe n vs ∧ c.eval vs≤1 ∧ (if c.eval vs=0 then b.Safe n vs else a.Safe n vs)

def compile (base : ι) : (e : Formula ι) → Realizer e.eval (fun n vs => e.Safe n vs)
  | .read i => Device.read i
  | .constant a => Device.constant base a
  | .add x y => Compose.realizer (compile base x) (compile base y) Device.add
  | .sub x y => Compose.realizer (compile base x) (compile base y) Device.subtract
  | .mul x y => Compose.realizer (compile base x) (compile base y) Device.multiply
  | .div x y => Compose.realizer (op:=Nat.div) (Adm:=fun n vs => 0<vs 1 ∧ 2*vs 1≤2^n) (compile base x) (compile base y) (Device.divide false)
  | .mod x y => Compose.realizer (op:=Nat.mod) (Adm:=fun n vs => 0<vs 1 ∧ 2*vs 1≤2^n) (compile base x) (compile base y) (Device.divide true)
  | .le x y => (Compose.realizer (Adm:=fun _ _ => True) (op:=fun a b => if b≤a then 1 else 0) (compile base y) (compile base x) Device.lessEqualReversed).weaken (fun n vs => (Formula.le x y).Safe n vs)
      (by intro n vs h;exact ⟨h.2,h.1,trivial⟩)
  | .powTwo x => composeUnary (compile base x) Device.powerTwo
  | .bitLength x => (composeUnary (compile base x) Device.bitLength).weaken (fun n vs => x.Safe n vs)
      (by intro n vs h;exact ⟨h,trivial⟩)
  | .branch c a b => Branch.realizer (compile base c) (compile base a) (compile base b)

 theorem operational (base : ι) (e : Formula ι) :
    ∃ (D : Realizer e.eval (fun n vs => e.Safe n vs)),
      ∀n,0<n → ∀xs,(∀i,(xs i).length=n) → e.Safe n (values xs) →
        ∃t y,t≤D.coefficient*(n+1)^2 ∧ y.length=n ∧ Binary.Add.value y.reverse=e.eval (values xs) ∧
          Run D.program (input xs) t (result xs D.out y) := by
  exact ⟨compile base e,(compile base e).spec⟩

end Formula
end SourceBurnside.Structured.Device

end

end OAI
