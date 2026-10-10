import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.UniversalInput

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def clear (k : K) : Program K := .loop k (fun _ => .skip)
def move (src dst : K) : Program K := .loop src (fun b => .push dst b)
def spread (src left right : K) : Program K :=
  .loop src (fun b => .seq (.push left b) (.push right b))
def copy (src dst tmp : K) : Program K := .seq (move src tmp) (spread tmp src dst)

lemma clear_run (k : K) (r : Store K) :
    Run (clear k) r (2*(r k).length+1) (Function.update r k []) := by
  generalize hv : r k=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update r k []=r := by rw [←hv];exact Function.update_eq_self k r
    rw [he]
    exact Run.loop_nil r k _ hv
  | append_singleton v a ih =>
    have hr : Function.update r k v k=v := Function.update_self ..
    have hh := Run.loop_cons r k (fun _ => Program.skip) v a
      (Function.update r k v) (Function.update (Function.update r k v) k [])
      1 (2*v.length+1) hv (Run.skip _) (ih _ hr)
    convert hh using 1 <;> simp [clear]
    omega

lemma move_run (src dst : K) (hne : src≠dst) (r : Store K) :
    Run (move src dst) r (2*(r src).length+1)
      (Function.update (Function.update r src []) dst (r dst++(r src).reverse)) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update r src []) dst (r dst++([]:List Bool).reverse)=r := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp
      · by_cases h2 : k=src
        · subst k;simp [hne,hv]
        · simp [h1,h2]
    rw [he]
    exact Run.loop_nil r src _ hv
  | append_singleton v a ih =>
    let r1 := Function.update r src v
    let r2 := Function.update r1 dst (r1 dst++[a])
    have h2 : r2 src=v := by simp [r2,r1,hne]
    have ht := ih r2 h2
    have hh := Run.loop_cons r src (fun b => Program.push dst b) v a r2
      (Function.update (Function.update r2 src []) dst (r2 dst++v.reverse))
      1 (2*v.length+1) hv (Run.push r1 dst a) ht
    have he : Function.update (Function.update r2 src []) dst (r2 dst++v.reverse)=
        Function.update (Function.update r src []) dst (r dst++(v++[a]).reverse) := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp [r2,r1,Ne.symm hne,List.reverse_append,List.append_assoc]
      · by_cases h2 : k=src
        · subst k;simp [h1]
        · simp [r2,r1,h1,h2]
    rw [he] at hh
    convert hh using 1 <;> simp [move]
    omega

lemma spread_run (src left right : K) (hsl : src≠left) (hsr : src≠right) (hlr : left≠right)
    (r : Store K) :
    Run (spread src left right) r (3*(r src).length+1)
      (Function.update (Function.update (Function.update r src []) left (r left++(r src).reverse))
        right (r right++(r src).reverse)) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update (Function.update r src []) left
        (r left++([]:List Bool).reverse)) right (r right++([]:List Bool).reverse)=r := by
      funext k
      by_cases h1 : k=right
      · subst k;simp
      · by_cases h2 : k=left
        · subst k;simp [h1]
        · by_cases h3 : k=src
          · subst k;simp [h1,h2,hv]
          · simp [h1,h2,h3]
    rw [he]
    exact Run.loop_nil r src _ hv
  | append_singleton v a ih =>
    let r1 := Function.update r src v
    let r2 := Function.update r1 left (r1 left++[a])
    let r3 := Function.update r2 right (r2 right++[a])
    have h3 : r3 src=v := by simp [r3,r2,r1,hsl,hsr]
    have ht := ih r3 h3
    have hb := Run.seq (.push left a) (.push right a) r1 r2 r3 1 1
      (Run.push r1 left a) (Run.push r2 right a)
    have hh := Run.loop_cons r src (fun b => Program.seq (.push left b) (.push right b)) v a r3
      (Function.update (Function.update (Function.update r3 src []) left (r3 left++v.reverse))
        right (r3 right++v.reverse))
      2 (3*v.length+1) hv hb ht
    have he : Function.update (Function.update (Function.update r3 src []) left (r3 left++v.reverse))
        right (r3 right++v.reverse)=
        Function.update (Function.update (Function.update r src []) left (r left++(v++[a]).reverse))
          right (r right++(v++[a]).reverse) := by
      funext k
      by_cases h1 : k=right
      · subst k;simp [r3,r2,r1,Ne.symm hlr,Ne.symm hsr,List.reverse_append,List.append_assoc]
      · by_cases h2 : k=left
        · subst k;simp [r3,r2,r1,hlr,Ne.symm hsl,List.reverse_append,List.append_assoc]
        · by_cases h3 : k=src
          · subst k;simp [h1,h2]
          · simp [r3,r2,r1,h1,h2,h3]
    rw [he] at hh
    convert hh using 1 <;> simp [spread]
    omega

lemma copy_run (src dst tmp : K) (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (r : Store K) (ht : r tmp=[]) :
    Run (copy src dst tmp) r (5*(r src).length+2)
      (Function.update r dst (r dst++r src)) := by
  let s := Function.update (Function.update r src []) tmp (r src).reverse
  have h1 : Run (move src tmp) r (2*(r src).length+1) s := by
    simpa [s,ht] using move_run src tmp hst r
  have h2 := spread_run tmp src dst (Ne.symm hst) (Ne.symm hdt) hsd s
  have hlen : (s tmp).length=(r src).length := by simp [s]
  rw [hlen] at h2
  have he : Function.update (Function.update (Function.update s tmp []) src (s src++(s tmp).reverse))
      dst (s dst++(s tmp).reverse)=Function.update r dst (r dst++r src) := by
    funext k
    by_cases h1 : k=dst
    · subst k;simp [s,hdt,Ne.symm hsd]
    · by_cases h2 : k=src
      · subst k;simp [s,h1,hst]
      · by_cases h3 : k=tmp
        · subst k;simp [s,h1,h2,ht]
        · simp [s,h1,h2,h3]
  rw [he] at h2
  have hh := Run.seq (move src tmp) (spread tmp src dst) r s _ _ _ h1 h2
  simpa only [copy,show (2*(r src).length+1)+(3*(r src).length+1)=5*(r src).length+2 by omega] using hh

end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Binary.Add
open Program
abbrev K := Fin 4

def bit (b : Bool) : ℕ := if b then 1 else 0
def value : List Bool → ℕ
  | [] => 0 | a::w => bit a+2*value w
def low (a b c : Bool) := (a ^^ b) ^^ c
def high (a b c : Bool) := (a && b) || (a && c) || (b && c)
lemma adder_equation (a b c : Bool) : bit (low a b c)+2*bit (high a b c)=bit a+bit b+bit c := by
  cases a <;> cases b <;> cases c <;> decide
lemma low_symm (a b c : Bool) : low a b c=low b a c := by cases a <;> cases b <;> rfl
lemma high_symm (a b c : Bool) : high a b c=high b a c := by cases a <;> cases b <;> cases c <;> rfl

lemma value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons a xs ih => simp [value,ih,Nat.pow_succ];ring

def store (xs ys out : List Bool) (c : Bool) : Store K := ![xs.reverse,ys.reverse,out,[c]]

def fullAdder (a b : Bool) : Program K := .pop 3 (fun z =>
  .seq (.push 2 (low a b (z.getD false))) (.push 3 (high a b (z.getD false))))
def step (a : Bool) : Program K := .pop 1 (fun z => fullAdder a (z.getD false))
def firstPass : Program K := .loop 0 step

def partialStore (xs ys out : List Bool) : Store K := ![xs.reverse,ys.reverse,out,[]]

lemma pop_carry (xs ys out : List Bool) (c : Bool) :
    Function.update (store xs ys out c) 3 []=partialStore xs ys out := by
  funext k;fin_cases k <;> simp [store,partialStore]
lemma fullAdder_push (xs ys out : List Bool) (a b c : Bool) :
    Function.update (Function.update (partialStore xs ys out) 2 (out++[low a b c])) 3
      [high a b c]=store xs ys (out++[low a b c]) (high a b c) := by
  funext k;fin_cases k <;> simp [store,partialStore]

lemma fullAdder_run (xs ys out : List Bool) (a b c : Bool) :
    Run (fullAdder a b) (store xs ys out c) 3 (store xs ys (out++[low a b c]) (high a b c)) := by
  let s := partialStore xs ys out
  let t := Function.update s 2 (out++[low a b c])
  have h1 := Run.push s (2:K) (low a b c)
  have h1' : Run (.push 2 (low a b c)) s 1 t := by simpa [s,t,partialStore] using h1
  have h2 := Run.push t (3:K) (high a b c)
  have h2' : Run (.push 3 (high a b c)) t 1 (store xs ys (out++[low a b c]) (high a b c)) := by
    have hh : t 3=[] := by simp [t,s,partialStore]
    rw [hh,List.nil_append] at h2
    simpa only [t,s,fullAdder_push] using h2
  have hs := Run.seq _ _ s t _ 1 1 h1' h2'
  unfold fullAdder
  refine Run.pop (store xs ys out c) (3:K) _ 2 _ ?_
  change Run (.seq (.push 2 (low a b c)) (.push 3 (high a b c)))
    (Function.update (store xs ys out c) 3 []) 2 _
  rw [pop_carry]
  exact hs

lemma pop_right (xs ys out : List Bool) (c : Bool) :
    Function.update (store xs ys out c) 1 ys.reverse.dropLast=store xs ys.tail out c := by
  funext k;fin_cases k <;> simp [store]
lemma pop_left (a : Bool) (xs ys out : List Bool) (c : Bool) :
    Function.update (store (a::xs) ys out c) 0 xs.reverse=store xs ys out c := by
  funext k;fin_cases k <;> simp [store]

lemma step_run (xs ys out : List Bool) (a c : Bool) :
    Run (step a) (store xs ys out c) 4
      (store xs ys.tail (out++[low a (ys.head?.getD false) c]) (high a (ys.head?.getD false) c)) := by
  unfold step
  refine Run.pop (store xs ys out c) (1:K) _ 3 _ ?_
  change Run (fullAdder a (ys.reverse.getLast?.getD false))
    (Function.update (store xs ys out c) 1 ys.reverse.dropLast) 3 _
  rw [List.getLast?_reverse,pop_right]
  exact fullAdder_run xs ys.tail out a (ys.head?.getD false) c

def scan : List Bool → List Bool → Bool → List Bool × List Bool × Bool
  | [],ys,c => ([],ys,c)
  | a::xs,ys,c =>
    let t := scan xs ys.tail (high a (ys.head?.getD false) c)
    (low a (ys.head?.getD false) c::t.1,t.2)

lemma scan_length (xs ys : List Bool) (c : Bool) : (scan xs ys c).1.length=xs.length := by
  induction xs generalizing ys c with
  | nil => rfl
  | cons a xs ih => simp [scan,ih]

lemma firstPass_run (xs ys out : List Bool) (c : Bool) :
    Run firstPass (store xs ys out c) (5*xs.length+1)
      (store [] (scan xs ys c).2.1 (out++(scan xs ys c).1) (scan xs ys c).2.2) := by
  induction xs generalizing ys out c with
  | nil => simpa [scan,firstPass] using Run.loop_nil (store [] ys out c) (0:K) step (by rfl)
  | cons a xs ih =>
    let b := ys.head?.getD false
    let last := scan xs ys.tail (high a b c)
    have hb : Run (step a) (Function.update (store (a::xs) ys out c) 0 xs.reverse) 4
        (store xs ys.tail (out++[low a b c]) (high a b c)) := by
      rw [pop_left];exact step_run xs ys out a c
    have ht := ih ys.tail (out++[low a b c]) (high a b c)
    have hh := Run.loop_cons (store (a::xs) ys out c) (0:K) step xs.reverse a _ _
      4 (5*xs.length+1) (by simp [store,List.reverse_cons]) hb ht
    convert hh using 1 <;> simp [firstPass,scan,b,List.append_assoc]
    omega

lemma scan_value (xs ys : List Bool) (c : Bool) :
    value xs+value ys+bit c =
      value (scan xs ys c).1+2^xs.length*(value (scan xs ys c).2.1+bit (scan xs ys c).2.2) := by
  induction xs generalizing ys c with
  | nil => simp [scan,value]
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hh := ih [] (high a false c)
      have hf := adder_equation a false c
      simp only [scan,List.head?_nil,Option.getD_none,List.tail_nil,value,List.length_cons,
        Nat.pow_succ] at *
      change bit (low a false c)+2*bit (high a false c)=bit a+0+bit c at hf
      nlinarith
    | cons b ys =>
      have hh := ih ys (high a b c)
      have hf := adder_equation a b c
      simp only [scan,List.head?_cons,Option.getD_some,List.tail_cons,value,List.length_cons,
        Nat.pow_succ] at *
      nlinarith

lemma scan_remaining (xs ys : List Bool) (c : Bool) : (scan xs ys c).2.1=ys.drop xs.length := by
  induction xs generalizing ys c with
  | nil => simp [scan]
  | cons a xs ih => cases ys <;> simp [scan,ih,List.drop_succ_cons]

lemma value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => simp [value]
  | cons a xs ih => cases a <;> simp [value,bit,Nat.pow_succ] <;> omega

def fixedAdd : Program K := .seq firstPass (Binary.move 2 0)

theorem fixedAdd_run (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length) :
    Run fixedAdd (store xs ys [] c) (7*xs.length+2)
      (store (scan xs ys c).1 [] [] (scan xs ys c).2.2) := by
  let z := (scan xs ys c).1
  let d := (scan xs ys c).2.2
  have he : (scan xs ys c).2.1=[] := by rw [scan_remaining,hlen,List.drop_length]
  have h1 : Run firstPass (store xs ys [] c) (5*xs.length+1) (store [] [] z d) := by
    simpa only [he,List.nil_append,z,d] using firstPass_run xs ys [] c
  have h2 := Binary.move_run (2:K) 0 (by decide) (store [] [] z d)
  have hh : Function.update (Function.update (store [] [] z d) 2 []) 0
      ((store [] [] z d) 0++((store [] [] z d) 2).reverse)=store z [] [] d := by
    funext k;fin_cases k <;> simp [store]
  rw [hh] at h2
  have hz : ((store [] [] z d) 2).length=xs.length := scan_length xs ys c
  rw [hz] at h2
  have H := Run.seq firstPass (Binary.move 2 0) _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

lemma scan_sum (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length) :
    value xs+value ys+bit c=value (scan xs ys c).1+2^xs.length*bit (scan xs ys c).2.2 := by
  have hr : (scan xs ys c).2.1=[] := by rw [scan_remaining,hlen,List.drop_length]
  simpa only [hr,value,Nat.zero_add] using scan_value xs ys c

lemma scan_mod (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length) :
    value (scan xs ys c).1=(value xs+value ys+bit c)%2^xs.length := by
  have hz := value_lt (scan xs ys c).1
  rw [scan_length] at hz
  rw [scan_sum xs ys c hlen,Nat.add_mod]
  simp only [Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hz]

lemma scan_exact (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length)
    (hbound : value xs+value ys+bit c<2^xs.length) :
    value (scan xs ys c).1=value xs+value ys+bit c ∧ (scan xs ys c).2.2=false := by
  constructor
  · rw [scan_mod xs ys c hlen,Nat.mod_eq_of_lt hbound]
  · have hh := scan_sum xs ys c hlen
    cases he : (scan xs ys c).2.2
    · rfl
    · rw [he] at hh
      change value xs+value ys+bit c=value (scan xs ys c).1+2^xs.length*1 at hh
      omega

end SourceBurnside.Structured.Binary.Add

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def mapMove (f : Bool → Bool) (src dst : K) : Program K := .loop src (fun b => .push dst (f b))
def mapInPlace (f : Bool → Bool) (src tmp : K) : Program K := .seq (mapMove f src tmp) (move tmp src)

lemma mapMove_run (f : Bool → Bool) (src dst : K) (hne : src≠dst) (r : Store K) :
    Run (mapMove f src dst) r (2*(r src).length+1)
      (Function.update (Function.update r src []) dst (r dst++((r src).reverse.map f))) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update r src []) dst (r dst++(([]:List Bool).reverse.map f))=r := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp
      · by_cases h2 : k=src
        · subst k;simp [hne,hv]
        · simp [h1,h2]
    rw [he]
    exact Run.loop_nil r src _ hv
  | append_singleton v a ih =>
    let r1 := Function.update r src v
    let r2 := Function.update r1 dst (r1 dst++[f a])
    have h2 : r2 src=v := by simp [r2,r1,hne]
    have ht := ih r2 h2
    have hh := Run.loop_cons r src (fun b => Program.push dst (f b)) v a r2
      (Function.update (Function.update r2 src []) dst (r2 dst++v.reverse.map f))
      1 (2*v.length+1) hv (Run.push r1 dst (f a)) ht
    have he : Function.update (Function.update r2 src []) dst (r2 dst++v.reverse.map f)=
        Function.update (Function.update r src []) dst (r dst++((v++[a]).reverse.map f)) := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp [r2,r1,Ne.symm hne,List.reverse_append,List.append_assoc]
      · by_cases h2 : k=src
        · subst k;simp [h1]
        · simp [r2,r1,h1,h2]
    rw [he] at hh
    convert hh using 1 <;> first | rfl | simp;omega

lemma mapInPlace_run (f : Bool → Bool) (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[]) :
    Run (mapInPlace f src tmp) r (4*(r src).length+2)
      (Function.update r src ((r src).map f)) := by
  let s := Function.update (Function.update r src []) tmp ((r src).reverse.map f)
  have h1 : Run (mapMove f src tmp) r (2*(r src).length+1) s := by
    simpa [s,ht] using mapMove_run f src tmp hne r
  have h2 := move_run tmp src (Ne.symm hne) s
  have he : Function.update (Function.update s tmp []) src (s src++(s tmp).reverse)=
      Function.update r src ((r src).map f) := by
    funext k
    by_cases h1 : k=src
    · subst k;simp [s,hne,List.map_reverse]
    · by_cases h2 : k=tmp
      · subst k;simp [h1,ht]
      · simp [s,h1,h2]
  rw [he] at h2
  have hl : (s tmp).length=(r src).length := by simp [s]
  rw [hl] at h2
  have H := Run.seq (mapMove f src tmp) (move tmp src) r s _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured
namespace Program
variable {K L : Type*}
def relabel (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .pop k b => .pop (f k) (fun a => relabel f (b a))
  | .seq p q => .seq (relabel f p) (relabel f q)
  | .loop k b => .loop (f k) (fun a => relabel f (b a))
end Program

variable {K L : Type*} [DecidableEq K] [DecidableEq L]
def Agrees (f : K → L) (r : Store K) (R : Store L) := ∀k,R (f k)=r k
def Outside (f : K → L) (R S : Store L) := ∀l,(∀k,f k≠l) → S l=R l

lemma agrees_update (f : K → L) (hf : Function.Injective f) (r : Store K) (R : Store L)
    (h : Agrees f r R) (k : K) (v : List Bool) :
    Agrees f (Function.update r k v) (Function.update R (f k) v) := by
  intro j
  by_cases he : j=k
  · subst j;simp
  · have hh : f j≠f k := fun e => he (hf e)
    simp [he,hh,h j]
omit [DecidableEq K] in
lemma outside_update (f : K → L) (R : Store L) (k : K) (v : List Bool) :
    Outside f R (Function.update R (f k) v) := by
  intro l hl
  exact Function.update_of_ne (Ne.symm (hl k)) v R
omit [DecidableEq K] [DecidableEq L] in
lemma outside_refl (f : K → L) (R : Store L) : Outside f R R := fun _ _ => rfl
omit [DecidableEq K] [DecidableEq L] in
lemma Outside.trans {f : K → L} {R S T : Store L} (h : Outside f R S) (h' : Outside f S T) :
    Outside f R T := fun l hl => (h' l hl).trans (h l hl)

theorem Run.relabel {P : Program K} {r s : Store K} {n : ℕ} (h : Run P r n s)
    (f : K → L) (hf : Function.Injective f) :
    ∀R,Agrees f r R → ∃S,Run (P.relabel f) R n S ∧ Agrees f s S ∧ Outside f R S := by
  induction h with
  | skip r => intro R hR;exact ⟨R,Run.skip R,hR,outside_refl f R⟩
  | push r k b =>
    intro R hR
    refine ⟨Function.update R (f k) (r k++[b]),?_,agrees_update f hf r R hR k _,outside_update f R k _⟩
    simpa only [Program.relabel,hR k] using Run.push R (f k) b
  | pop r k b n s h ih =>
    intro R hR
    obtain ⟨S,hS,ha,ho⟩ := ih (Function.update R (f k) (r k).dropLast)
      (agrees_update f hf r R hR k _)
    refine ⟨S,?_,ha,(outside_update f R k _).trans ho⟩
    unfold Program.relabel
    refine Run.pop R (f k) _ n S ?_
    simpa only [hR k] using hS
  | seq p q r s t n m hp hq ihp ihq =>
    intro R hR
    obtain ⟨S,hS,ha,ho⟩ := ihp R hR
    obtain ⟨T,hT,hb,hp⟩ := ihq S ha
    exact ⟨T,Run.seq _ _ R S T n m hS hT,hb,ho.trans hp⟩
  | loop_nil r k b hr =>
    intro R hR
    exact ⟨R,Run.loop_nil R (f k) _ ((hR k).trans hr),hR,outside_refl f R⟩
  | loop_cons r k b v a s t n m hr hb ht ihb iht =>
    intro R hR
    obtain ⟨S,hS,ha,ho⟩ := ihb (Function.update R (f k) v) (agrees_update f hf r R hR k v)
    obtain ⟨T,hT,hb,hp⟩ := iht S ha
    refine ⟨T,Run.loop_cons R (f k) _ v a S T n m ((hR k).trans hr) hS hT,
      hb,((outside_update f R k v).trans ho).trans hp⟩

end SourceBurnside.Structured

namespace SourceBurnside.Structured.Binary.Add
open Program
lemma complement_value (xs : List Bool) : value xs+value (xs.map not)=2^xs.length-1 := by
  induction xs with
  | nil => simp [value]
  | cons a xs ih =>
    have hp : 0<2^xs.length := by positivity
    cases a <;> simp only [List.map_cons, value, List.length_cons, Bool.not_false, Bool.not_true, bit, Bool.false_eq_true, ↓reduceIte, Nat.pow_succ] at * <;> omega

lemma subtract_equation (xs ys : List Bool) (hlen : xs.length=ys.length) :
    value xs+2^xs.length = value ys+value (scan xs (ys.map not) true).1+
      2^xs.length*bit (scan xs (ys.map not) true).2.2 := by
  have h := scan_sum xs (ys.map not) true (by simp [hlen])
  have hy := complement_value ys
  have hp : 0<2^ys.length := by positivity
  change value xs+value (ys.map not)+1= _ at h
  rw [hlen] at h ⊢
  omega

lemma subtract_carry (xs ys : List Bool) (hlen : xs.length=ys.length) :
    (scan xs (ys.map not) true).2.2=true ↔ value ys≤value xs := by
  have hh := subtract_equation xs ys hlen
  have hz := value_lt (scan xs (ys.map not) true).1
  rw [scan_length] at hz
  cases he : (scan xs (ys.map not) true).2.2 <;>
    simp [he,bit] at hh <;> simp <;> omega

lemma subtract_exact (xs ys : List Bool) (hlen : xs.length=ys.length) (hle : value ys≤value xs) :
    value (scan xs (ys.map not) true).1=value xs-value ys := by
  have hh := subtract_equation xs ys hlen
  rw [(subtract_carry xs ys hlen).mpr hle] at hh
  simp only [bit,ite_true,Nat.mul_one] at hh
  omega

def fixedSubtract : Program K := .seq (Binary.mapInPlace not 1 2) fixedAdd

theorem fixedSubtract_run (xs ys : List Bool) (hlen : xs.length=ys.length) :
    Run fixedSubtract (store xs ys [] true) (11*xs.length+4)
      (store (scan xs (ys.map not) true).1 [] [] (scan xs (ys.map not) true).2.2) := by
  have h1 := Binary.mapInPlace_run not (1:K) 2 (by decide) (store xs ys [] true) (by rfl)
  have he : Function.update (store xs ys [] true) 1 ((store xs ys [] true 1).map not)=
      store xs (ys.map not) [] true := by
    funext k;fin_cases k <;> simp [store,List.map_reverse]
  rw [he] at h1
  have hl : (store xs ys [] true 1).length=xs.length := by simp [store,hlen]
  rw [hl] at h1
  have h2 := fixedAdd_run xs (ys.map not) true (by simp [hlen])
  have H := Run.seq (Binary.mapInPlace not 1 2) fixedAdd _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

end SourceBurnside.Structured.Binary.Add

namespace SourceBurnside.Structured
open Program
variable {K L : Type*} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
lemma agrees_outside_unique (f : K → L) (R S T : Store L) (s : Store K)
    (hS : Agrees f s S) (hT : Agrees f s T) (oS : Outside f R S) (oT : Outside f R T) : S=T := by
  funext l
  by_cases h : ∃k,f k=l
  · obtain ⟨k,rfl⟩ := h
    exact (hS k).trans (hT k).symm
  · have hn : ∀k,f k≠l := by simpa using h
    exact (oS l hn).trans (oT l hn).symm

lemma Run.relabel_to {P : Program K} {r s : Store K} {n : ℕ} (h : Run P r n s)
    (f : K → L) (hf : Function.Injective f) (R S : Store L)
    (ha : Agrees f r R) (hb : Agrees f s S) (ho : Outside f R S) :
    Run (P.relabel f) R n S := by
  obtain ⟨T,hT,hb',ho'⟩ := h.relabel f hf R ha
  rwa [agrees_outside_unique f R T S s hb' hb ho' ho] at hT

namespace Binary

def patch4 (f : Fin 4 → K) (r : Store K) (s : Store (Fin 4)) : Store K :=
  Function.update (Function.update (Function.update (Function.update r (f 0) (s 0)) (f 1) (s 1))
    (f 2) (s 2)) (f 3) (s 3)

lemma patch4_agrees (f : Fin 4 → K) (hf : Function.Injective f) (r : Store K) (s : Store (Fin 4)) :
    Agrees f s (patch4 f r s) := by
  intro k
  have hi : ∀i j : Fin 4, i≠j → f i≠f j := fun _ _ h => hf.ne h
  fin_cases k <;> simp [patch4,hi]

lemma patch4_outside (f : Fin 4 → K) (r : Store K) (s : Store (Fin 4)) :
    Outside f r (patch4 f r s) := by
  intro k hk
  simp [patch4,Ne.symm (hk 0),Ne.symm (hk 1),Ne.symm (hk 2),Ne.symm (hk 3)]

lemma patch4_run {P : Program (Fin 4)} {r s : Store (Fin 4)} {n : ℕ} (h : Run P r n s)
    (f : Fin 4 → K) (hf : Function.Injective f) (R : Store K) (ha : Agrees f r R) :
    Run (P.relabel f) R n (patch4 f R s) :=
  h.relabel_to f hf R _ ha (patch4_agrees f hf R s) (patch4_outside f R s)

lemma fixedAdd_call (f : Fin 4 → K) (hf : Function.Injective f) (R : Store K)
    (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length)
    (ha : Agrees f (Add.store xs ys [] c) R) :
    Run (Add.fixedAdd.relabel f) R (7*xs.length+2)
      (patch4 f R (Add.store (Add.scan xs ys c).1 [] [] (Add.scan xs ys c).2.2)) :=
  patch4_run (Add.fixedAdd_run xs ys c hlen) f hf R ha

end Binary
end SourceBurnside.Structured

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def dropFront (src tmp : K) : Program K :=
  .seq (move src tmp) (.pop tmp (fun _ => move tmp src))
def shift (src tmp : K) : Program K := .seq (dropFront src tmp) (.push src false)

lemma dropFront_run (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[]) :
    Run (dropFront src tmp) r (2*(r src).length+2*(r src).tail.length+3)
      (Function.update r src (r src).tail) := by
  let s := Function.update (Function.update r src []) tmp (r src).reverse
  let s' := Function.update s tmp (r src).reverse.dropLast
  have h1 : Run (move src tmp) r (2*(r src).length+1) s := by
    simpa [s,ht] using move_run src tmp hne r
  have h2 := move_run tmp src (Ne.symm hne) s'
  have he : Function.update (Function.update s' tmp []) src (s' src++(s' tmp).reverse)=
      Function.update r src (r src).tail := by
    funext k
    by_cases hk : k=src
    · subst k;simp [s',s,hne]
    · by_cases hkt : k=tmp
      · subst k;simp [s',s,ht,hk]
      · simp [s',s,hk,hkt]
  rw [he] at h2
  have hl : (s' tmp).length=(r src).tail.length := by simp [s',List.length_tail]
  rw [hl] at h2
  have h2' : Run (.pop tmp (fun _ => move tmp src)) s (1+(2*(r src).tail.length+1))
      (Function.update r src (r src).tail) := by
    refine Run.pop s tmp _ _ _ ?_
    simpa only [s',s,Function.update_self] using h2
  have H := Run.seq (move src tmp) (.pop tmp (fun _ => move tmp src)) _ _ _ _ _ h1 h2'
  convert H using 1 <;> first | rfl | omega

lemma shift_run (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[])
    (hx : r src≠[]) :
    Run (shift src tmp) r (4*(r src).length+2)
      (Function.update r src ((r src).tail++[false])) := by
  have h1 := dropFront_run src tmp hne r ht
  have h2 := Run.push (Function.update r src (r src).tail) src false
  simp only [Function.update_self,Function.update_idem] at h2
  have H := Run.seq (dropFront src tmp) (.push src false) _ _ _ _ _ h1 h2
  have hn : 0<(r src).length := List.length_pos_iff.mpr hx
  have hl := List.length_tail (l:=r src)
  convert H using 1 <;> first | rfl | omega

namespace Add

def double (xs : List Bool) := false::xs.dropLast
lemma double_length (xs : List Bool) (hx : xs≠[]) : (double xs).length=xs.length := by
  have hn := List.length_pos_iff.mpr hx
  simp [double,List.length_dropLast];omega
lemma double_reverse (xs : List Bool) : (double xs).reverse=xs.reverse.tail++[false] := by
  simp [double,List.reverse_cons]

lemma double_value (xs : List Bool) (hx : xs≠[]) :
    value (double xs)=(2*value xs)%2^xs.length := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (hx rfl)
  | append_singleton xs a ih =>
    have hval : value (double (xs++[a]))=2*value xs := by simp [double,value,bit]
    rw [hval,value_append]
    have he : 2*(value xs+2^xs.length*value [a])=2*value xs+2^(xs++[a]).length*value [a] := by
      simp [Nat.pow_succ];ring
    rw [he,Nat.add_mod]
    have hb : 2*value xs<2^(xs++[a]).length := by
      have hv := value_lt xs
      simp [Nat.pow_succ];omega
    simp only [Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt hb]

end Add
end SourceBurnside.Structured.Binary

end

end OAI
