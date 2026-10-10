import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.BinaryRegisters

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary.Multiply
open Program
abbrev K := Fin 6

def store (acc x y : List Bool) : Store K := ![acc.reverse,x.reverse,y.reverse,[],[],[]]
def regs : Fin 4 → K := ![0,3,4,5]
lemma regs_injective : Function.Injective regs := by decide

def addX : Program K :=
  .seq (copy 1 3 4) (.seq (.push 5 false) (.seq (Add.fixedAdd.relabel regs) (clear 5)))

def addStore (acc x y : List Bool) (c : List Bool) : Store K := ![acc.reverse,x.reverse,y.reverse,x.reverse,[],c]
def carryStore (acc x y : List Bool) (c : Bool) : Store K := ![acc.reverse,x.reverse,y.reverse,[],[],[c]]

lemma addX_run (acc x y : List Bool) (hlen : acc.length=x.length) :
    Run addX (store acc x y) (12*x.length+8) (store (Add.scan acc x false).1 x y) := by
  have h1 := copy_run (1:K) 3 4 (by decide) (by decide) (by decide) (store acc x y) (by rfl)
  have he1 : Function.update (store acc x y) 3 ((store acc x y) 3++(store acc x y) 1)=
      addStore acc x y [] := by funext k;fin_cases k <;> simp [store,addStore]
  rw [he1] at h1
  have hl1 : (store acc x y 1).length=x.length := by simp [store]
  rw [hl1] at h1
  have h2 := Run.push (addStore acc x y []) (5:K) false
  have he2 : Function.update (addStore acc x y []) 5 ((addStore acc x y []) 5++[false])=
      addStore acc x y [false] := by funext k;fin_cases k <;> simp [addStore]
  rw [he2] at h2
  let z := (Add.scan acc x false).1
  let c := (Add.scan acc x false).2.2
  have h3 := fixedAdd_call regs regs_injective (addStore acc x y [false]) acc x false hlen (by
    intro k;fin_cases k <;> rfl)
  have he3 : patch4 regs (addStore acc x y [false]) (Add.store z [] [] c)=carryStore z x y c := by
    funext k;fin_cases k <;> simp [patch4,regs,Add.store,carryStore,addStore]
  rw [he3,hlen] at h3
  have h4 := clear_run (5:K) (carryStore z x y c)
  have he4 : Function.update (carryStore z x y c) 5 []=store z x y := by
    funext k;fin_cases k <;> simp [carryStore,store]
  rw [he4] at h4
  change Run (clear (5:K)) (carryStore z x y c) 3 (store z x y) at h4
  have H := Run.seq (copy 1 3 4) _ _ _ _ _ _ h1
    (Run.seq (.push 5 false) _ _ _ _ _ _ h2
    (Run.seq (Add.fixedAdd.relabel regs) (clear 5) _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

def plusIf (b : Bool) (acc x : List Bool) : List Bool := if b then (Add.scan acc x false).1 else acc

def step (b : Bool) : Program K := .seq (if b then addX else .skip) (shift 1 4)
def stepCost (b : Bool) (n : ℕ) : ℕ := if b then 16*n+10 else 4*n+3

lemma step_run (b : Bool) (acc x y : List Bool) (hlen : acc.length=x.length) (hx : x≠[]) :
    Run (step b) (store acc x y) (stepCost b x.length) (store (plusIf b acc x) (Add.double x) y) := by
  have h1 : Run (if b then addX else .skip) (store acc x y)
      (if b then 12*x.length+8 else 1) (store (plusIf b acc x) x y) := by
    cases b
    · exact Run.skip _
    · exact addX_run acc x y hlen
  have h2 := shift_run (1:K) 4 (by decide) (store (plusIf b acc x) x y) (by rfl)
    (by simpa [store] using hx)
  have he2 : Function.update (store (plusIf b acc x) x y) 1
      ((store (plusIf b acc x) x y 1).tail++[false])=store (plusIf b acc x) (Add.double x) y := by
    funext k;fin_cases k <;> simp [store,Add.double_reverse]
  rw [he2] at h2
  have hl : (store (plusIf b acc x) x y 1).length=x.length := by simp [store]
  rw [hl] at h2
  have H := Run.seq (if b then addX else .skip) (shift 1 4) _ _ _ _ _ h1 h2
  cases b <;> convert H using 1 <;> first | rfl | simp [stepCost];omega

def scan : List Bool → List Bool → List Bool → List Bool × List Bool
  | acc,x,[] => (acc,x)
  | acc,x,b::ys => scan (plusIf b acc x) (Add.double x) ys

def time (n : ℕ) : List Bool → ℕ
  | [] => 1
  | b::ys => 1+stepCost b n+time n ys

def program : Program K := .loop 2 step

lemma plusIf_length (b : Bool) (acc x : List Bool) : (plusIf b acc x).length=acc.length := by
  cases b <;> simp [plusIf,Add.scan_length]

lemma scan_length (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    (scan acc x y).1.length=acc.length ∧ (scan acc x y).2.length=x.length := by
  induction y generalizing acc x with
  | nil => exact ⟨rfl,rfl⟩
  | cons b y ih =>
    have hp := plusIf_length b acc x
    have hd := Add.double_length x hx
    obtain ⟨h1,h2⟩ := ih (plusIf b acc x) (Add.double x) (by simp [Add.double]) (by omega)
    change (scan (plusIf b acc x) (Add.double x) y).1.length=acc.length ∧
      (scan (plusIf b acc x) (Add.double x) y).2.length=x.length
    exact ⟨h1.trans hp,h2.trans hd⟩

lemma program_run (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    Run program (store acc x y) (time x.length y) (store (scan acc x y).1 (scan acc x y).2 []) := by
  induction y generalizing acc x with
  | nil => exact Run.loop_nil (store acc x []) (2:K) step (by rfl)
  | cons b ys ih =>
    have hp := plusIf_length b acc x
    have hd := Add.double_length x hx
    have ht := ih (plusIf b acc x) (Add.double x) (by simp [Add.double]) (by omega)
    have hs := step_run b acc x ys hlen hx
    have he : Function.update (store acc x (b::ys)) 2 ys.reverse=store acc x ys := by
      funext k;fin_cases k <;> simp [store]
    have hb : Run (step b) (Function.update (store acc x (b::ys)) 2 ys.reverse) (stepCost b x.length)
        (store (plusIf b acc x) (Add.double x) ys) := by rw [he];exact hs
    rw [hd] at ht
    have H := Run.loop_cons (store acc x (b::ys)) (2:K) step ys.reverse b _ _ _ _
      (by simp [store,List.reverse_cons]) hb ht
    convert H using 1 <;> first | rfl | simp [time];omega

lemma time_bound (n : ℕ) (ys : List Bool) : time n ys≤ys.length*(16*n+11)+1 := by
  induction ys with
  | nil => simp [time]
  | cons b ys ih => cases b <;> simp [time,stepCost] <;> nlinarith

lemma plusIf_modEq (b : Bool) (acc x : List Bool) (hlen : acc.length=x.length) :
    Nat.ModEq (2^x.length) (Add.value (plusIf b acc x)) (Add.value acc+Add.bit b*Add.value x) := by
  cases b
  · simp only [plusIf,Bool.false_eq_true,↓reduceIte,Add.bit,Nat.zero_mul,Nat.add_zero]
    exact Nat.ModEq.rfl
  · simp only [plusIf,↓reduceIte,Add.bit,Nat.one_mul]
    rw [Add.scan_mod acc x false hlen]
    simp only [Add.bit,Bool.false_eq_true,↓reduceIte,Nat.add_zero,hlen]
    exact Nat.mod_modEq _ _

lemma scan_modEq (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    Nat.ModEq (2^x.length) (Add.value (scan acc x y).1) (Add.value acc+Add.value x*Add.value y) := by
  induction y generalizing acc x with
  | nil => simp [scan,Add.value,Nat.ModEq]
  | cons b ys ih =>
    have hp := plusIf_length b acc x
    have hd := Add.double_length x hx
    have hi := ih (plusIf b acc x) (Add.double x) (by simp [Add.double]) (by omega)
    rw [hd] at hi
    have hxmod : Nat.ModEq (2^x.length) (Add.value (Add.double x)) (2*Add.value x) := by
      rw [Add.double_value x hx];exact Nat.mod_modEq _ _
    have hm := (plusIf_modEq b acc x hlen).add (hxmod.mul_right (Add.value ys))
    have he : Add.value acc+Add.bit b*Add.value x+2*Add.value x*Add.value ys=
        Add.value acc+Add.value x*Add.value (b::ys) := by simp only [Add.value];ring
    rw [he] at hm
    exact hi.trans hm

lemma scan_value (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    Add.value (scan acc x y).1=(Add.value acc+Add.value x*Add.value y)%2^x.length := by
  have h := scan_modEq acc x y hx hlen
  change Add.value (scan acc x y).1%2^x.length=_ at h
  have hb := Add.value_lt (scan acc x y).1
  rw [(scan_length acc x y hx hlen).1,hlen] at hb
  rwa [Nat.mod_eq_of_lt hb] at h

end SourceBurnside.Structured.Binary.Multiply

namespace SourceBurnside.Structured.Binary
open Program

def roll {K : Type*} (src tmp : K) (b : Bool) : Program K := .seq (dropFront src tmp) (.push src b)
def rollBits (b : Bool) (xs : List Bool) := b::xs.dropLast
lemma rollBits_length (b : Bool) (xs : List Bool) (hx : xs≠[]) : (rollBits b xs).length=xs.length := by
  have hn := List.length_pos_iff.mpr hx
  simp [rollBits,List.length_dropLast];omega
lemma rollBits_reverse (b : Bool) (xs : List Bool) : (rollBits b xs).reverse=xs.reverse.tail++[b] := by
  simp [rollBits,List.reverse_cons]
lemma roll_run {K : Type*} [DecidableEq K] (src tmp : K) (hne : src≠tmp) (b : Bool)
    (r : Store K) (ht : r tmp=[]) (hx : r src≠[]) :
    Run (roll src tmp b) r (4*(r src).length+2)
      (Function.update r src ((r src).tail++[b])) := by
  have h1 := dropFront_run src tmp hne r ht
  have h2 := Run.push (Function.update r src (r src).tail) src b
  simp only [Function.update_self,Function.update_idem] at h2
  have H := Run.seq (dropFront src tmp) (.push src b) _ _ _ _ _ h1 h2
  have hn : 0<(r src).length := List.length_pos_iff.mpr hx
  have hl := List.length_tail (l:=r src)
  convert H using 1 <;> first | rfl | omega

lemma rollBits_value (b : Bool) (xs : List Bool) (hx : xs≠[]) :
    Add.value (rollBits b xs)=(2*Add.value xs+Add.bit b)%2^xs.length := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (hx rfl)
  | append_singleton xs a ih =>
    have hval : Add.value (rollBits b (xs++[a]))=2*Add.value xs+Add.bit b := by
      simp [rollBits,Add.value];omega
    rw [hval,Add.value_append]
    have he : 2*(Add.value xs+2^xs.length*Add.value [a])+Add.bit b=
        (2*Add.value xs+Add.bit b)+2^(xs++[a]).length*Add.value [a] := by
      simp [Nat.pow_succ];ring
    rw [he,Nat.add_mod]
    have hb : 2*Add.value xs+Add.bit b<2^(xs++[a]).length := by
      have hv := Add.value_lt xs
      cases b <;> simp [Nat.pow_succ,Add.bit] <;> omega
    simp only [Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hb]

namespace Divide
abbrev K := Fin 8

def store (q r d ys : List Bool) : Store K := ![q.reverse,r.reverse,d.reverse,ys.reverse,[],[],[],[]]
def scratchStore (q r d ys v w c : List Bool) : Store K :=
  ![q.reverse,r.reverse,d.reverse,ys.reverse,v.reverse,w.reverse,[],c]
def trialStore (q r d ys z : List Bool) (c : Bool) : Store K :=
  scratchStore q r d ys z [] [c]
def regs : Fin 4 → K := ![4,5,6,7]
lemma regs_injective : Function.Injective regs := by decide

def choose (c : Bool) : Program K :=
  .seq (if c then .seq (clear 1) (copy 4 1 6) else .skip)
    (.seq (clear 4) (roll 0 6 c))
def chooseTime (c : Bool) (n : ℕ) : ℕ := if c then 13*n+6 else 6*n+4

lemma choose_run (q r d ys z : List Bool) (c : Bool)
    (hqr : q.length=r.length) (hz : z.length=r.length) (hr : r≠[]) :
    Run (choose c) (scratchStore q r d ys z [] []) (chooseTime c r.length)
      (store (rollBits c q) (if c then z else r) d ys) := by
  let s := scratchStore q (if c then z else r) d ys z [] []
  have h1 : Run (if c then .seq (clear 1) (copy 4 1 6) else .skip)
      (scratchStore q r d ys z [] []) (if c then 7*r.length+3 else 1) s := by
    cases c
    · exact Run.skip _
    · change Run _ _ (7*r.length+3) s
      have ha := clear_run (1:K) (scratchStore q r d ys z [] [])
      let a := scratchStore q [] d ys z [] []
      have he : Function.update (scratchStore q r d ys z [] []) 1 []=a := by
        funext k;fin_cases k <;> simp [a,scratchStore]
      rw [he] at ha
      have hl : (scratchStore q r d ys z [] [] 1).length=r.length := by simp [scratchStore]
      rw [hl] at ha
      have hb := copy_run (4:K) 1 6 (by decide) (by decide) (by decide) a (by rfl)
      have he' : Function.update a 1 (a 1++a 4)=s := by
        funext k;fin_cases k <;> simp [a,s,scratchStore]
      rw [he'] at hb
      have hl' : (a 4).length=r.length := by simp [a,scratchStore,hz]
      rw [hl'] at hb
      have H := Run.seq (clear 1) (copy 4 1 6) _ _ _ _ _ ha hb
      convert H using 1 <;> first | rfl | omega
  have h2 := clear_run (4:K) s
  have he2 : Function.update s 4 []=store q (if c then z else r) d ys := by
    funext k;fin_cases k <;> simp [s,scratchStore,store]
  rw [he2] at h2
  have hl2 : (s 4).length=r.length := by simp [s,scratchStore,hz]
  rw [hl2] at h2
  have hqn : q≠[] := by intro he;have hn := List.length_pos_iff.mpr hr;simp [he] at hqr;omega
  have h3 := roll_run (0:K) 6 (by decide) c (store q (if c then z else r) d ys) (by rfl)
    (by simpa [store] using hqn)
  have he3 : Function.update (store q (if c then z else r) d ys) 0
      ((store q (if c then z else r) d ys 0).tail++[c])=
      store (rollBits c q) (if c then z else r) d ys := by
    funext k;fin_cases k <;> simp [store,rollBits_reverse]
  rw [he3] at h3
  have hl3 : (store q (if c then z else r) d ys 0).length=r.length := by simp [store,hqr]
  rw [hl3] at h3
  have H := Run.seq (if c then .seq (clear 1) (copy 4 1 6) else .skip) _ _ _ _ _ _ h1
    (Run.seq (clear 4) (roll 0 6 c) _ _ _ _ _ h2 h3)
  cases c <;> convert H using 1 <;> first | rfl | simp [chooseTime];omega

def trial (r d : List Bool) := Add.scan r (d.map not) true
def carry (r d : List Bool) := (trial r d).2.2

def makeTrial : Program K := .seq (copy 1 4 6) (.seq (copy 2 5 6)
  (.seq (.push 7 true) (Add.fixedSubtract.relabel regs)))

lemma makeTrial_run (q r d ys : List Bool) (hrd : r.length=d.length) :
    Run makeTrial (store q r d ys) (21*r.length+9)
      (trialStore q r d ys (trial r d).1 (carry r d)) := by
  have h1 := copy_run (1:K) 4 6 (by decide) (by decide) (by decide) (store q r d ys) (by rfl)
  have he1 : Function.update (store q r d ys) 4 ((store q r d ys) 4++(store q r d ys) 1)=
      scratchStore q r d ys r [] [] := by funext k;fin_cases k <;> simp [store,scratchStore]
  rw [he1] at h1
  have hl1 : (store q r d ys 1).length=r.length := by simp [store]
  rw [hl1] at h1
  have h2 := copy_run (2:K) 5 6 (by decide) (by decide) (by decide)
    (scratchStore q r d ys r [] []) (by rfl)
  have he2 : Function.update (scratchStore q r d ys r [] []) 5
      ((scratchStore q r d ys r [] []) 5++(scratchStore q r d ys r [] []) 2)=
      scratchStore q r d ys r d [] := by funext k;fin_cases k <;> simp [scratchStore]
  rw [he2] at h2
  have hl2 : (scratchStore q r d ys r [] [] 2).length=r.length := by simp [scratchStore,hrd]
  rw [hl2] at h2
  have h3 := Run.push (scratchStore q r d ys r d []) (7:K) true
  have he3 : Function.update (scratchStore q r d ys r d []) 7
      ((scratchStore q r d ys r d []) 7++[true])=scratchStore q r d ys r d [true] := by
    funext k;fin_cases k <;> simp [scratchStore]
  rw [he3] at h3
  have h4 := patch4_run (Add.fixedSubtract_run r d hrd) regs regs_injective
    (scratchStore q r d ys r d [true]) (by intro k;fin_cases k <;> rfl)
  have he4 : patch4 regs (scratchStore q r d ys r d [true])
      (Add.store (Add.scan r (d.map not) true).1 [] [] (Add.scan r (d.map not) true).2.2)=
      trialStore q r d ys (trial r d).1 (carry r d) := by
    funext k;fin_cases k <;> simp [patch4,regs,Add.store,trialStore,scratchStore,trial,carry]
  rw [he4] at h4
  have H := Run.seq (copy 1 4 6) _ _ _ _ _ _ h1
    (Run.seq (copy 2 5 6) _ _ _ _ _ _ h2
    (Run.seq (.push 7 true) (Add.fixedSubtract.relabel regs) _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

def oneStep (b : Bool) (q r d : List Bool) : List Bool × List Bool :=
  let r' := rollBits b r
  let c := carry r' d
  (rollBits c q, if c then (trial r' d).1 else r')
def step (b : Bool) : Program K := .seq (roll 1 6 b)
  (.seq makeTrial (.pop 7 (fun c => choose (c.getD false))))
def stepTime (b : Bool) (r d : List Bool) : ℕ :=
  25*r.length+12+chooseTime (carry (rollBits b r) d) r.length

lemma oneStep_lengths (b : Bool) (q r d : List Bool) (hqr : q.length=r.length) (hr : r≠[]) :
    (oneStep b q r d).1.length=q.length ∧ (oneStep b q r d).2.length=r.length := by
  have hqn : q≠[] := by intro he;have hn := List.length_pos_iff.mpr hr;simp [he] at hqr;omega
  have hr' := rollBits_length b r hr
  constructor
  · exact rollBits_length _ q hqn
  · unfold oneStep;simp only
    split <;> simp only [trial,Add.scan_length,hr']

lemma step_run (b : Bool) (q r d ys : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) :
    Run (step b) (store q r d ys) (stepTime b r d)
      (store (oneStep b q r d).1 (oneStep b q r d).2 d ys) := by
  let r' := rollBits b r
  have hrlen : r'.length=r.length := rollBits_length b r hr
  have hr'n : r'≠[] := by simp [r',rollBits]
  have h1 := roll_run (1:K) 6 (by decide) b (store q r d ys) (by rfl)
    (by simpa [store] using hr)
  have he1 : Function.update (store q r d ys) 1 ((store q r d ys 1).tail++[b])=store q r' d ys := by
    funext k;fin_cases k <;> simp [store,r',rollBits_reverse]
  rw [he1] at h1
  have hl1 : (store q r d ys 1).length=r.length := by simp [store]
  rw [hl1] at h1
  have h2 := makeTrial_run q r' d ys (hrlen.trans hrd)
  let c := carry r' d
  let z := (trial r' d).1
  have hz : z.length=r'.length := Add.scan_length r' (d.map not) true
  have h3 := choose_run q r' d ys z c (hqr.trans hrlen.symm) hz hr'n
  have he3 : Function.update (trialStore q r' d ys z c) 7
      ((trialStore q r' d ys z c) 7).dropLast=scratchStore q r' d ys z [] [] := by
    funext k;fin_cases k <;> simp [trialStore,scratchStore]
  have h3' : Run (.pop 7 (fun c => choose (c.getD false))) (trialStore q r' d ys z c)
      (1+chooseTime c r'.length) (store (rollBits c q) (if c then z else r') d ys) := by
    refine Run.pop _ (7:K) _ _ _ ?_
    change Run (choose c) _ _ _
    rw [he3];exact h3
  have H := Run.seq (roll 1 6 b) _ _ _ _ _ _ h1
    (Run.seq makeTrial (.pop 7 (fun c => choose (c.getD false))) _ _ _ _ _ h2 h3')
  rw [hrlen] at H
  convert H using 1 <;> first | rfl | simp [stepTime,r',c];omega

def scan (q r d : List Bool) : List Bool → List Bool × List Bool
  | [] => (q,r)
  | b::ys => scan (oneStep b q r d).1 (oneStep b q r d).2 d ys

def time (q r d : List Bool) : List Bool → ℕ
  | [] => 1
  | b::ys => 1+stepTime b r d+time (oneStep b q r d).1 (oneStep b q r d).2 d ys

def program : Program K := .loop 3 step

lemma scan_lengths (q r d ys : List Bool) (hqr : q.length=r.length) (hr : r≠[]) :
    (scan q r d ys).1.length=q.length ∧ (scan q r d ys).2.length=r.length := by
  induction ys generalizing q r with
  | nil => exact ⟨rfl,rfl⟩
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have hh := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) hn
    exact ⟨hh.1.trans h.1,hh.2.trans h.2⟩

lemma program_run (q r d ys : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) :
    Run program (store q r d ys) (time q r d ys) (store (scan q r d ys).1 (scan q r d ys).2 d []) := by
  induction ys generalizing q r with
  | nil => exact Run.loop_nil (store q r d []) (3:K) step (by rfl)
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have ht := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) (h.2.trans hrd) hn
    have hs := step_run b q r d ys hqr hrd hr
    have he : Function.update (store q r d (b::ys)) 3 ys.reverse=store q r d ys := by
      funext k;fin_cases k <;> simp [store]
    have hb : Run (step b) (Function.update (store q r d (b::ys)) 3 ys.reverse) (stepTime b r d)
        (store (oneStep b q r d).1 (oneStep b q r d).2 d ys) := by rw [he];exact hs
    have H := Run.loop_cons (store q r d (b::ys)) (3:K) step ys.reverse b _ _ _ _
      (by simp [store,List.reverse_cons]) hb ht
    convert H using 1 <;> first | rfl | simp [time];omega

lemma time_bound (q r d ys : List Bool) (hqr : q.length=r.length) (hr : r≠[]) :
    time q r d ys≤ys.length*(38*r.length+19)+1 := by
  induction ys generalizing q r with
  | nil => simp [time]
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have hh := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) hn
    have hs : stepTime b r d≤38*r.length+18 := by
      unfold stepTime chooseTime;split <;> omega
    rw [h.2] at hh
    simp only [time,List.length_cons]
    nlinarith

lemma oneStep_value (b : Bool) (q r d : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) (hd : 0<Add.value d)
    (_hds : 2*Add.value d≤2^r.length) (hrem : Add.value r<Add.value d)
    (hbound : 2*(Add.value q*Add.value d+Add.value r)+Add.bit b<2^r.length) :
    Add.value (oneStep b q r d).1*Add.value d+Add.value (oneStep b q r d).2=
      2*(Add.value q*Add.value d+Add.value r)+Add.bit b ∧
    Add.value (oneStep b q r d).2<Add.value d := by
  let r' := rollBits b r
  let c := carry r' d
  let z := if c then (trial r' d).1 else r'
  have hrlen : r'.length=d.length := (rollBits_length b r hr).trans hrd
  have hb : Add.bit b≤1 := by cases b <;> decide
  have hrb : 2*Add.value r+Add.bit b<2^r.length := by omega
  have hrv : Add.value r'=2*Add.value r+Add.bit b := by
    rw [rollBits_value b r hr,Nat.mod_eq_of_lt hrb]
  have hc : c=true ↔ Add.value d≤Add.value r' := Add.subtract_carry r' d hrlen
  have hz : Add.value z+Add.bit c*Add.value d=Add.value r' ∧ Add.value z<Add.value d := by
    cases he : c
    · have hn : Add.value r'<Add.value d := by rw [he] at hc;simp at hc;omega
      simp only [z,he,Bool.false_eq_true,↓reduceIte,Add.bit,Nat.zero_mul,Nat.add_zero]
      exact ⟨trivial,hn⟩
    · have hn : Add.value d≤Add.value r' := hc.mp he
      have hv := Add.subtract_exact r' d hrlen hn
      change Add.value (trial r' d).1=Add.value r'-Add.value d at hv
      simp only [z,he,↓reduceIte,Add.bit,Nat.one_mul]
      rw [hv]
      constructor <;> omega
  have hbalance : (2*Add.value q+Add.bit c)*Add.value d+Add.value z=
      2*(Add.value q*Add.value d+Add.value r)+Add.bit b := by nlinarith [hz.1]
  have hqb : 2*Add.value q+Add.bit c<2^r.length := by
    have hh : 2*Add.value q+Add.bit c≤(2*Add.value q+Add.bit c)*Add.value d := by
      exact Nat.le_mul_of_pos_right _ hd
    omega
  have hqn : q≠[] := by intro he;have hn := List.length_pos_iff.mpr hr;simp [he] at hqr;omega
  have hqv : Add.value (rollBits c q)=2*Add.value q+Add.bit c := by
    rw [rollBits_value c q hqn,hqr,Nat.mod_eq_of_lt hqb]
  change Add.value (rollBits c q)*Add.value d+Add.value z=_ ∧ Add.value z<Add.value d
  rw [hqv]
  exact ⟨hbalance,hz.2⟩

def feed (N : ℕ) : List Bool → ℕ
  | [] => N
  | b::ys => feed (2*N+Add.bit b) ys

lemma feed_le (N : ℕ) (ys : List Bool) : N≤feed N ys := by
  induction ys generalizing N with
  | nil => rfl
  | cons b ys ih => exact (by omega : N≤2*N+Add.bit b).trans (ih _)

lemma feed_value (N : ℕ) (ys : List Bool) : feed N ys=2^ys.length*N+Add.value ys.reverse := by
  induction ys generalizing N with
  | nil => simp [feed,Add.value]
  | cons b ys ih => simp only [feed,ih,List.length_cons,Nat.pow_succ,List.reverse_cons,
      Add.value_append,List.length_reverse,Add.value];ring

lemma scan_value (q r d ys : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) (hd : 0<Add.value d)
    (hds : 2*Add.value d≤2^r.length) (hrem : Add.value r<Add.value d)
    (hbound : feed (Add.value q*Add.value d+Add.value r) ys<2^r.length) :
    Add.value (scan q r d ys).1*Add.value d+Add.value (scan q r d ys).2=
      feed (Add.value q*Add.value d+Add.value r) ys ∧
    Add.value (scan q r d ys).2<Add.value d := by
  induction ys generalizing q r with
  | nil => exact ⟨rfl,hrem⟩
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have hb : 2*(Add.value q*Add.value d+Add.value r)+Add.bit b<2^r.length :=
      (feed_le _ ys).trans_lt hbound
    have hv := oneStep_value b q r d hqr hrd hr hd hds hrem hb
    have hd' : 2*Add.value d≤2^(oneStep b q r d).2.length := by rw [h.2];exact hds
    have hb' : feed (Add.value (oneStep b q r d).1*Add.value d+Add.value (oneStep b q r d).2) ys<
        2^(oneStep b q r d).2.length := by rw [hv.1,h.2];exact hbound
    have hh := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) (h.2.trans hrd) hn hd' hv.2 hb'
    simpa only [scan,feed,hv.1] using hh

lemma zero_value (n : ℕ) : Add.value (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,Add.value,Add.bit,ih]

theorem division (d ys : List Bool) (hd : 0<Add.value d) (hds : 2*Add.value d≤2^d.length)
    (hinput : Add.value ys.reverse<2^d.length) :
    let z := List.replicate d.length false
    let result := scan z z d ys
    Add.value result.1=Add.value ys.reverse/Add.value d ∧
    Add.value result.2=Add.value ys.reverse%Add.value d ∧
    ∃n,n≤ys.length*(38*d.length+19)+1 ∧ Run program (store z z d ys) n (store result.1 result.2 d []) := by
  dsimp only
  let z := List.replicate d.length false
  have hdlen : 0<d.length := by
    by_contra h;have he : d=[] := List.length_eq_zero_iff.mp (by omega)
    simp [he,Add.value] at hd
  have hz : z≠[] := by simp [z,hdlen.ne']
  have hzl : z.length=d.length := by simp [z]
  have hzv : Add.value z=0 := zero_value d.length
  have hb : feed (Add.value z*Add.value d+Add.value z) ys<2^z.length := by
    simpa only [hzv,Nat.zero_mul,Nat.add_zero,feed_value,Nat.mul_zero,Nat.zero_add,hzl] using hinput
  have hv := scan_value z z d ys rfl hzl hz hd (hzl ▸ hds) (by rw [hzv];exact hd) hb
  simp only [hzv,Nat.zero_mul,Nat.zero_add,feed_value,Nat.mul_zero] at hv
  have hdiv : Add.value ys.reverse/Add.value d=Add.value (scan z z d ys).1 :=
    Nat.div_eq_of_lt_le (by nlinarith [hv.1]) (by nlinarith [hv.1,hv.2])
  have hmod : Add.value ys.reverse%Add.value d=Add.value (scan z z d ys).2 := by
    have hh := Nat.mod_add_div (Add.value ys.reverse) (Add.value d)
    rw [hdiv] at hh;nlinarith [hv.1]
  refine ⟨hdiv.symm,hmod.symm,time z z d ys,?_,program_run z z d ys rfl hzl hz⟩
  simpa only [hzl] using time_bound z z d ys rfl hz

end Divide
end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Device
open Program Binary

variable {ι : Type} [DecidableEq ι]

def input {W : Type} (xs : ι → List Bool) : Store (ι ⊕ W) := Sum.elim xs (fun _ => [])
def values (xs : ι → List Bool) : ι → ℕ := fun i => Add.value (xs i).reverse

def result {W : Type} [DecidableEq W] (xs : ι → List Bool) (out : W) (y : List Bool) : Store (ι ⊕ W) :=
  Function.update (input xs) (.inr out) y

structure Realizer (f : (ι → ℕ) → ℕ) (Pre : ℕ → (ι → ℕ) → Prop) where
  W : Type
  finiteW : Finite W
  eqW : DecidableEq W
  out : W
  program : Program (ι ⊕ W)
  coefficient : ℕ
  spec : ∀ (n : ℕ) (_hn : 0<n) (xs : ι → List Bool),
    (∀i,(xs i).length=n) → Pre n (values xs) →
    ∃t y,t≤coefficient*(n+1)^2 ∧ y.length=n ∧ Add.value y.reverse=f (values xs) ∧
      Run program (input xs) t (@result ι _ W eqW xs out y)
attribute [instance] Realizer.finiteW Realizer.eqW

variable {f : (ι → ℕ) → ℕ} {Pre : ℕ → (ι → ℕ) → Prop}

lemma Realizer.transport {L : Type} [DecidableEq L] (D : Realizer f Pre)
    (e : ι ⊕ D.W → L) (he : Function.Injective e) (n : ℕ) (hn : 0<n)
    (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n) (hPre : Pre n (values xs))
    (R : Store L) (hi : ∀i,R (e (.inl i))=xs i) (hw : ∀w,R (e (.inr w))=[]) :
    ∃t y,t≤D.coefficient*(n+1)^2 ∧ y.length=n ∧ Add.value y.reverse=f (values xs) ∧
      Run (D.program.relabel e) R t (Function.update R (e (.inr D.out)) y) := by
  obtain ⟨t,y,ht,hy,hv,hr⟩ := D.spec n hn xs hxs hPre
  have ha : Agrees e (input xs) R := by intro k;cases k <;> simp_all [input]
  exact ⟨t,y,ht,hy,hv,hr.relabel_to e he R _ ha
    (agrees_update e he (input xs) R ha (.inr D.out) y) (outside_update e R (.inr D.out) y)⟩

namespace Compose
variable {g : (ι → ℕ) → ℕ} {Q : ℕ → (ι → ℕ) → Prop}
variable {op : ℕ → ℕ → ℕ} {Adm : ℕ → (Fin 2 → ℕ) → Prop}
variable (F : Realizer f Pre) (G : Realizer g Q)
variable (O : Realizer (fun ab : Fin 2 → ℕ => op (ab 0) (ab 1)) Adm)

abbrev Work := F.W ⊕ (G.W ⊕ O.W)

def left : ι ⊕ F.W → ι ⊕ Work F G O := Sum.map id Sum.inl
def right : ι ⊕ G.W → ι ⊕ Work F G O := Sum.map id (Sum.inr ∘ Sum.inl)
def call : Fin 2 ⊕ O.W → ι ⊕ Work F G O
  | .inl i => if i=0 then .inr (.inl F.out) else .inr (.inr (.inl G.out))
  | .inr w => .inr (.inr (.inr w))

lemma left_injective : Function.Injective (left F G O) := by
  intro firstValue secondValue equality
  cases firstValue <;> cases secondValue <;>
    simp_all [-Sum.update_elim_inr, -Sum.elim_update_right, left]
lemma right_injective : Function.Injective (right F G O) := by
  intro firstValue secondValue equality
  cases firstValue <;> cases secondValue <;>
    simp_all [-Sum.update_elim_inr, -Sum.elim_update_right, right]
lemma call_injective : Function.Injective (call F G O) := by
  intro x y h
  cases x with
  | inl i => cases y with
    | inl j => fin_cases i <;> fin_cases j <;> simp_all [call]
    | inr w => fin_cases i <;> simp_all [call]
  | inr v => cases y with
    | inl j => fin_cases j <;> simp_all [call]
    | inr w => simpa [-Sum.update_elim_inr, -Sum.elim_update_right, call] using h

def body : Program (ι ⊕ Work F G O) :=
  .seq (F.program.relabel (left F G O)) (.seq (G.program.relabel (right F G O))
    (.seq (O.program.relabel (call F G O))
      (.seq (clear (.inr (.inl F.out))) (clear (.inr (.inr (.inl G.out)))))))

lemma body_run (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n)
    (hF : Pre n (values xs)) (hG : Q n (values xs))
    (hO : Adm n ![f (values xs),g (values xs)]) :
    ∃t y,t≤(F.coefficient+G.coefficient+O.coefficient+6)*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=op (f (values xs)) (g (values xs)) ∧
      Run (body F G O) (input xs) t (result xs (.inr (.inr O.out)) y) := by
  let R : Store (ι ⊕ Work F G O) := input xs
  obtain ⟨tf,yf,htf,hyf,hvf,hf⟩ := F.transport (left F G O) (left_injective F G O)
    n hn xs hxs hF R (by intro i;rfl) (by intro w;rfl)
  let Rf := Function.update R (.inr (.inl F.out)) yf
  change Run (F.program.relabel (left F G O)) R tf Rf at hf
  obtain ⟨tg,yg,htg,hyg,hvg,hg⟩ := G.transport (right F G O) (right_injective F G O)
    n hn xs hxs hG Rf (by intro i;simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rf,R,input,right]) (by intro w;simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rf,R,input,right])
  let Rg := Function.update Rf (.inr (.inr (.inl G.out))) yg
  change Run (G.program.relabel (right F G O)) Rf tg Rg at hg
  let ab : Fin 2 → List Bool := ![yf,yg]
  have hab : ∀i,(ab i).length=n := by intro i;fin_cases i <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, ab,hyf,hyg]
  have hav : values ab=![f (values xs),g (values xs)] := by
    funext i;fin_cases i
    · exact hvf
    · exact hvg
  obtain ⟨top,yo,hto,hyo,hvo,ho⟩ := O.transport (call F G O) (call_injective F G O) n hn ab hab
    (by rw [hav];exact hO) Rg (by intro i;fin_cases i <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rg,Rf,call,ab])
    (by intro w;simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rg,Rf,R,input,call])
  let Ro := Function.update Rg (.inr (.inr (.inr O.out))) yo
  change Run (O.program.relabel (call F G O)) Rg top Ro at ho
  have hclearF := clear_run (.inr (.inl F.out)) Ro
  let Ra := Function.update Ro (.inr (.inl F.out)) []
  have hcleanFlen : (Ro (.inr (.inl F.out))).length=n := by simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ro,Rg,Rf,hyf]
  rw [hcleanFlen] at hclearF
  have hclearG := clear_run (.inr (.inr (.inl G.out))) Ra
  have hcleanGlen : (Ra (.inr (.inr (.inl G.out)))).length=n := by simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,hyg]
  rw [hcleanGlen] at hclearG
  have he : Function.update Ra (.inr (.inr (.inl G.out))) []=result xs (.inr (.inr O.out)) yo := by
    funext k
    cases k with
    | inl i => simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input]
    | inr w => cases w with
      | inl w => by_cases hw : w=F.out <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input,hw]
      | inr w => cases w with
        | inl w => by_cases hw : w=G.out <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input,hw]
        | inr w => simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input]
  rw [he] at hclearG
  have H := Run.seq (F.program.relabel (left F G O)) _ _ _ _ _ _ hf
    (Run.seq (G.program.relabel (right F G O)) _ _ _ _ _ _ hg
    (Run.seq (O.program.relabel (call F G O)) _ _ _ _ _ _ ho
    (Run.seq (clear (.inr (.inl F.out))) (clear (.inr (.inr (.inl G.out)))) _ _ _ _ _ hclearF hclearG)))
  refine ⟨tf+(tg+(top+((2*n+1)+(2*n+1)))),yo,?_,hyo,?_,H⟩
  · nlinarith
  · simpa only [hav,Matrix.cons_val_zero,Matrix.cons_val_one] using hvo

def realizer : Realizer (fun vs => op (f vs) (g vs))
    (fun n vs => Pre n vs ∧ Q n vs ∧ Adm n ![f vs,g vs]) where
  W := Work F G O
  finiteW := inferInstance
  eqW := inferInstance
  out := .inr (.inr O.out)
  program := body F G O
  coefficient := F.coefficient+G.coefficient+O.coefficient+6
  spec := by
    intro n hn xs hxs h
    exact body_run F G O n hn xs hxs h.1 h.2.1 h.2.2

end Compose

def read (i : ι) : Realizer (fun vs => vs i) (fun _ _ => True) where
  W := Fin 2
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := copy (.inl i) (.inr 0) (.inr 1)
  coefficient := 7
  spec := by
    intro n hn xs hxs _
    have h := copy_run (.inl i) (.inr (0:Fin 2)) (.inr 1) (by simp) (by simp) (by simp)
      (input xs) (by rfl)
    have hl : (input (W:=Fin 2) xs (.inl i)).length=n := hxs i
    rw [hl] at h
    change Run (copy (.inl i) (.inr (0:Fin 2)) (.inr 1)) (input xs) (5*n+2)
      (result xs 0 (xs i)) at h
    exact ⟨5*n+2,xs i,by nlinarith,hxs i,rfl,h⟩

end SourceBurnside.Structured.Device

end

end OAI
