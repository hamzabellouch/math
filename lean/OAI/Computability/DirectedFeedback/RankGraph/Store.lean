import Mathlib
import OAI.Computability.DirectedFeedback.Model

namespace OAI


section

namespace DirectedFeedback.StackDSL
open Turing

variable {K S : Type} [DecidableEq K]

structure Store (K S : Type) where
  state : S
  tape : K → List Bool

inductive Prim (K S : Type)
  | push (k : K) (value : S → Bool)
  | pop (k : K) (update : S → Option Bool → S)
  | peek (k : K) (update : S → Option Bool → S)
  | load (update : S → S)

namespace Prim

def run : Prim K S → Store K S → Store K S
  | .push k f, s => ⟨s.state, Function.update s.tape k (f s.state :: s.tape k)⟩
  | .pop k f, s => ⟨f s.state (s.tape k).head?, Function.update s.tape k (s.tape k).tail⟩
  | .peek k f, s => ⟨f s.state (s.tape k).head?, s.tape⟩
  | .load f, s => ⟨f s.state,s.tape⟩

end Prim

inductive Code (K S : Type)
  | atom (p : Prim K S)
  | seq (first second : Code K S)
  | branch (test : S → Bool) (yes no : Code K S)
  | scan (input : K) (update : S → Bool → S) (body : Code K S)

namespace Code

theorem iterate_sum {A : Type} (f : A → A) (n m : Nat) (a : A) :
    f^[n+m] a = f^[m] (f^[n] a) := by
  rw [Nat.add_comm,Function.iterate_add_apply]

@[reducible] def Label : Code K S → Type
  | .atom _ => Unit
  | .seq c d => Label c ⊕ Label d
  | .branch _ c d => Unit ⊕ (Label c ⊕ Label d)
  | .scan _ _ c => Unit ⊕ Label c

noncomputable instance labelFintype (c : Code K S) : Fintype c.Label := by
  induction c with
  | atom => exact inferInstanceAs (Fintype Unit)
  | seq c d ihc ihd => exact @instFintypeSum c.Label d.Label ihc ihd
  | branch f c d ihc ihd =>
    exact @instFintypeSum Unit (c.Label ⊕ d.Label) inferInstance
      (@instFintypeSum c.Label d.Label ihc ihd)
  | scan k f c ih => exact @instFintypeSum Unit c.Label inferInstance ih

@[reducible] def entry : (c : Code K S) → c.Label
  | .atom _ => ()
  | .seq c _ => .inl c.entry
  | .branch _ _ _ => .inl ()
  | .scan _ _ _ => .inl ()

def ret {L : Type} (exit : Option L) : TM2.Stmt (fun _ : K => Bool) L (S × Option Bool) :=
  match exit with
  | none => .halt
  | some l => .goto (fun _ => l)

@[simp] theorem ret_eval {L : Type} (exit : Option L) (s : S × Option Bool)
    (t : K → List Bool) : TM2.stepAux (ret exit) s t = ⟨exit,s,t⟩ := by
  cases exit <;> rfl

def primitive {L : Type} (p : Prim K S) (exit : Option L) :
    TM2.Stmt (fun _ : K => Bool) L (S × Option Bool) :=
  match p with
  | .push k f => .push k (fun s => f s.1) (ret exit)
  | .pop k f => .pop k (fun s x => (f s.1 x,s.2)) (ret exit)
  | .peek k f => .peek k (fun s x => (f s.1 x,s.2)) (ret exit)
  | .load f => .load (fun s => (f s.1,s.2)) (ret exit)

def compile {L : Type} : (c : Code K S) → (c.Label → L) → Option L →
    c.Label → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool)
  | .atom p, _, exit, _ => primitive p exit
  | .seq c d, label, _, .inl i =>
    c.compile (fun j => label (.inl j)) (some (label (.inr d.entry))) i
  | .seq _ d, label, exit, .inr i =>
    d.compile (fun j => label (.inr j)) exit i
  | .branch f c d, label, _, .inl _ =>
    .branch (fun s => f s.1) (.goto fun _ => label (.inr (.inl c.entry)))
      (.goto fun _ => label (.inr (.inr d.entry)))
  | .branch _ c _, label, exit, .inr (.inl i) =>
    c.compile (fun j => label (.inr (.inl j))) exit i
  | .branch _ _ d, label, exit, .inr (.inr i) =>
    d.compile (fun j => label (.inr (.inr j))) exit i
  | .scan k update c, label, exit, .inl _ =>
    .pop k (fun s x => (s.1,x))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.2.elim s.1 (update s.1),none))
          (.goto fun _ => label (.inr c.entry)))
        (.load (fun s => (s.1,none)) (ret exit)))
  | .scan _ _ c, label, _, .inr i =>
    c.compile (fun j => label (.inr j)) (some (label (.inl ()))) i

inductive Exec : Code K S → Store K S → Nat → Store K S → Prop
  | atom (p : Prim K S) (s : Store K S) : Exec (.atom p) s 1 (p.run s)
  | seq {c d : Code K S} {s t u : Store K S} {n m : Nat} :
    Exec c s n t → Exec d t m u → Exec (.seq c d) s (n+m) u
  | branch_true {f : S → Bool} {c d : Code K S} {s t : Store K S} {n : Nat} :
    f s.state = true → Exec c s n t → Exec (.branch f c d) s (1+n) t
  | branch_false {f : S → Bool} {c d : Code K S} {s t : Store K S} {n : Nat} :
    f s.state = false → Exec d s n t → Exec (.branch f c d) s (1+n) t
  | scan_nil {k : K} {f : S → Bool → S} {c : Code K S} {s : Store K S} :
    s.tape k = [] → Exec (.scan k f c) s 1 s
  | scan_cons {k : K} {f : S → Bool → S} {c : Code K S}
      {s t u : Store K S} {b : Bool} {rest : List Bool} {n m : Nat} :
    s.tape k = b :: rest →
    Exec c ⟨f s.state b,Function.update s.tape k rest⟩ n t →
    Exec (.scan k f c) t m u → Exec (.scan k f c) s (1+n+m) u

def cfg {L : Type} (l : Option L) (s : Store K S) :
    TM2.Cfg (fun _ : K => Bool) L (S × Option Bool) := ⟨l,(s.state,none),s.tape⟩

def advance {L : Type} (program : L → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool))
    (s : Option (TM2.Cfg (fun _ : K => Bool) L (S × Option Bool))) := s.bind (TM2.step program)

@[simp] theorem advance_some {L : Type} (program : L → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool))
    (s : TM2.Cfg (fun _ : K => Bool) L (S × Option Bool)) :
    advance program (some s) = TM2.step program s := rfl

theorem Exec.trace {c : Code K S} {s t : Store K S} {n : Nat} (h : Exec c s n t)
    {L : Type} (label : c.Label → L) (exit : Option L)
    (program : L → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool))
    (atLabel : ∀ i, program (label i) = c.compile label exit i) :
    (advance program)^[n] (some (cfg (some (label c.entry)) s)) = some (cfg exit t) := by
  induction h generalizing L with
  | atom p s =>
    simp only [Function.iterate_one,advance_some,cfg,TM2.step]
    rw [atLabel]
    cases p <;> simp [compile,primitive,Prim.run]
  | @seq c d s t u n m hc hd ihc ihd =>
    rw [iterate_sum]
    dsimp only [entry]
    rw [ihc (fun i => label (.inl i)) (some (label (.inr d.entry))) program
      (fun i => atLabel (.inl i))]
    exact ihd (fun i => label (.inr i)) exit program (fun i => atLabel (.inr i))
  | @branch_true f c d s t n hf hc ih =>
    rw [iterate_sum]
    have first : advance program (some (cfg (some (label (.inl ()))) s)) =
        some (cfg (some (label (.inr (.inl c.entry)))) s) := by
      simp only [advance_some,cfg,TM2.step]
      rw [atLabel (.inl ())]
      simp only [compile,TM2.stepAux,hf,Bool.cond_true]
    simp only [Function.iterate_one,entry]
    change (advance program)^[n] (advance program (some (cfg _ s))) = _
    rw [first]
    exact ih _ exit program (fun i => atLabel (.inr (.inl i)))
  | @branch_false f c d s t n hf hd ih =>
    rw [iterate_sum]
    have first : advance program (some (cfg (some (label (.inl ()))) s)) =
        some (cfg (some (label (.inr (.inr d.entry)))) s) := by
      simp only [advance_some,cfg,TM2.step]
      rw [atLabel (.inl ())]
      simp only [compile,TM2.stepAux,hf,Bool.cond_false]
    simp only [Function.iterate_one,entry]
    change (advance program)^[n] (advance program (some (cfg _ s))) = _
    rw [first]
    exact ih _ exit program (fun i => atLabel (.inr (.inr i)))
  | @scan_nil k f c s hs =>
    simp only [Function.iterate_one,advance_some,cfg,TM2.step,entry]
    rw [atLabel (.inl ())]
    simp only [compile,TM2.stepAux,hs,List.head?_nil,List.tail_nil,
      Option.isSome_none,Bool.cond_false,ret_eval]
    congr 2
    exact Function.update_eq_self_iff.mpr hs.symm
  | @scan_cons k f c s t u b rest n m hs hc hl ihc ihl =>
    have first : advance program (some (cfg (some (label (.inl ()))) s)) =
        some (cfg (some (label (.inr c.entry)))
          ⟨f s.state b,Function.update s.tape k rest⟩) := by
      simp only [advance_some,cfg,TM2.step]
      rw [atLabel (.inl ())]
      simp only [compile,TM2.stepAux,hs,
        List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.elim_some]
    rw [iterate_sum,iterate_sum]
    change (advance program)^[m] ((advance program)^[n]
      (advance program (some (cfg (some (label (.inl ()))) s)))) = _
    rw [first,ihc (fun i => label (.inr i)) (some (label (.inl ()))) program
      (fun i => atLabel (.inr i))]
    exact ihl label exit program atLabel

end Code
end DirectedFeedback.StackDSL

namespace DirectedFeedback.StackDSL
open Turing
namespace Code
variable {K S : Type} [DecidableEq K] [Fintype K] [Fintype S]

def ioStore (initial : S) (k : K) (input : List Bool) : Store K S :=
  ⟨initial,fun j => if j = k then input else []⟩

@[reducible] noncomputable def machine (c : Code K S) (initial : S) (input output : K) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := fun _ => Bool
  Λ := c.Label
  main := c.entry
  σ := S × Option Bool
  initialState := (initial,none)
  m := c.compile id none

theorem machine_init (c : Code K S) (initial : S) (input output : K) (bits : List Bool) :
    initList (c.machine initial input output) bits = cfg (some c.entry) (ioStore initial input bits) := by
  rfl

theorem machine_halt (c : Code K S) (initial : S) (input output : K) (bits : List Bool) :
    haltList (c.machine initial input output) bits = cfg none (ioStore initial output bits) := by
  rfl

noncomputable def computation {A B : Type} (ea : A → List Bool) (eb : B → List Bool)
    (f : A → B) (c : Code K S) (initial : S) (input output : K)
    (time : Polynomial Nat) (cost : A → Nat)
    (runs : ∀ a, c.Exec (ioStore initial input (ea a)) (cost a) (ioStore initial output (eb (f a))))
    (bound : ∀ a, cost a ≤ time.eval (ea a).length) :
    TM2ComputableInPolyTime ea eb f where
  tm := c.machine initial input output
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun a := {
    steps := cost a
    evals_in_steps := by
      simp only [Equiv.refl, List.map_id, Option.map_some]
      change (advance (c.compile id none))^[cost a]
        (some (initList (c.machine initial input output) (ea a))) =
          some (haltList (c.machine initial input output) (eb (f a)))
      rw [machine_init,machine_halt]
      exact (runs a).trace id none (c.compile id none) (fun _ => rfl)
    steps_le_m := bound a }

end Code
end DirectedFeedback.StackDSL

end


namespace DirectedFeedback.StackDSL
open Code
variable {K : Type} [DecidableEq K]

namespace Store

def put (s : Store K Bool) (k : K) (value : List Bool) : Store K Bool :=
  ⟨s.state,Function.update s.tape k value⟩
def flag (s : Store K Bool) (value : Bool) : Store K Bool := ⟨value,s.tape⟩

@[simp] theorem put_tape_same (s : Store K Bool) (k : K) (v : List Bool) : (s.put k v).tape k = v := by
  simp [put]
@[simp] theorem put_tape_other (s : Store K Bool) {k j : K} (h : j ≠ k) (v : List Bool) :
    (s.put k v).tape j = s.tape j := by simp [put,h]
@[simp] theorem put_state (s : Store K Bool) (k : K) (v : List Bool) : (s.put k v).state = s.state := rfl
omit [DecidableEq K] in
@[simp] theorem flag_state (s : Store K Bool) (b : Bool) : (s.flag b).state = b := rfl
omit [DecidableEq K] in
@[simp] theorem flag_tape (s : Store K Bool) (b : Bool) : (s.flag b).tape = s.tape := rfl
@[simp] theorem put_put (s : Store K Bool) (k : K) (v w : List Bool) : (s.put k v).put k w = s.put k w := by
  simp [put]
@[simp] theorem put_self (s : Store K Bool) (k : K) : s.put k (s.tape k) = s := by
  cases s
  simp [put]
omit [DecidableEq K] in
@[simp] theorem flag_flag (s : Store K Bool) (b c : Bool) : (s.flag b).flag c = s.flag c := rfl
omit [DecidableEq K] in
@[simp] theorem flag_self (s : Store K Bool) : s.flag s.state = s := by cases s; rfl
@[simp] theorem put_flag (s : Store K Bool) (k : K) (v : List Bool) (b : Bool) :
    (s.flag b).put k v = (s.put k v).flag b := rfl

theorem put_comm (s : Store K Bool) {k j : K} (h : k ≠ j) (v w : List Bool) :
    (s.put k v).put j w = (s.put j w).put k v := by
  simp [put,Function.update_comm h]

omit [DecidableEq K] in
@[ext] theorem ext (s t : Store K Bool) (hs : s.state = t.state) (ht : s.tape = t.tape) : s=t := by
  cases s; cases t; simp_all

end Store

namespace Ops

@[reducible] def idle : Code K Bool := .atom (.load id)
@[reducible] def reset : Code K Bool := .atom (.load fun _ => false)
@[reducible] def push (k : K) (b : Bool) : Code K Bool := .atom (.push k fun _ => b)
@[reducible] def pop (k : K) : Code K Bool := .atom (.pop k fun s _ => s)
@[reducible] def clear (k : K) : Code K Bool := .scan k (fun s _ => s) idle

theorem idle_run (s : Store K Bool) : idle.Exec s 1 s := by
  exact Exec.atom (.load id) s

theorem reset_run (s : Store K Bool) : reset.Exec s 1 (s.flag false) := by
  exact Exec.atom (.load fun _ => false) s

theorem push_run (s : Store K Bool) (k : K) (b : Bool) :
    (push k b).Exec s 1 (s.put k (b::s.tape k)) := by
  exact Exec.atom (.push k fun _ => b) s

theorem pop_run (s : Store K Bool) (k : K) :
    (pop k).Exec s 1 (s.put k (s.tape k).tail) := by
  exact Exec.atom (.pop k fun s _ => s) s

theorem clear_list (k : K) (s : Store K Bool) (l : List Bool) :
    (clear k).Exec (s.put k l) (2*l.length+1) (s.put k []) := by
  induction l with
  | nil => simpa using (Exec.scan_nil (c := idle) (f := fun s _ => s)
      (s := s.put k []) (by simp))
  | cons b l ih =>
    have h : (clear k).Exec (s.put k (b::l)) (1+1+(2*l.length+1)) (s.put k []) := by
      apply Exec.scan_cons (b := b) (rest := l) (by simp)
      · change idle.Exec ((s.put k (b::l)).put k l) 1 (s.put k l)
        simpa using idle_run (s.put k l)
      · exact ih
    convert h using 1; simp; omega

theorem clear_run (k : K) (s : Store K Bool) :
    (clear k).Exec s (2*(s.tape k).length+1) (s.put k []) := by
  simpa using clear_list k s (s.tape k)

@[reducible] def transferScan (src dst : K) : Code K Bool := .scan src (fun _ b => b) (.atom (.push dst id))
@[reducible] def transfer (src dst : K) : Code K Bool := .seq (transferScan src dst) reset

theorem transferScan_run (src dst : K) (hne : src ≠ dst) (l d : List Bool) (s : Store K Bool) :
    ∃ b, (transferScan src dst).Exec ((s.put src l).put dst d) (2*l.length+1)
      (((s.put src []).put dst (l.reverse++d)).flag b) := by
  induction l generalizing d s with
  | nil =>
    refine ⟨s.state,?_⟩
    simpa [transferScan,Store.put,Store.flag] using (Exec.scan_nil (c := .atom (.push dst id)) (f := fun _ b => b)
      (s := (s.put src []).put dst d) (by simp [hne]))
  | cons b l ih =>
    obtain ⟨q,hq⟩ := ih (b::d) (s.flag b)
    refine ⟨q,?_⟩
    have hbody : (.atom (.push dst id) : Code K Bool).Exec
        ⟨b,Function.update (((s.put src (b::l)).put dst d).tape) src l⟩ 1
        (((s.flag b).put src l).put dst (b::d)) := by
      convert Exec.atom (.push dst id)
        (⟨b,Function.update (((s.put src (b::l)).put dst d).tape) src l⟩ : Store K Bool) using 1
      refine Store.ext _ _ ?_ ?_
      · rfl
      funext k
      by_cases hs : k = src <;> by_cases hd : k = dst <;>
        simp_all [Prim.run,Store.put,Store.flag,Function.update_apply]
    have h := Exec.scan_cons (k := src) (f := fun _ b => b)
      (c := .atom (.push dst id))
      (s := (s.put src (b::l)).put dst d) (b := b) (rest := l) (by simp [hne]) hbody hq
    convert h using 1 <;> simp [List.reverse_cons,List.append_assoc]; omega

theorem transfer_run (src dst : K) (hne : src ≠ dst) (s : Store K Bool) :
    (transfer src dst).Exec s (2*(s.tape src).length+2)
      (((s.put src []).put dst ((s.tape src).reverse++s.tape dst)).flag false) := by
  obtain ⟨b,h⟩ := transferScan_run src dst hne (s.tape src) (s.tape dst) s
  simp only [Store.put_self] at h
  have hh := Exec.seq h (reset_run _)
  convert hh using 1; simp

@[reducible] def fanScan (src a b : K) (f g : Bool → Bool) : Code K Bool :=
  .scan src (fun _ x => x) (.seq (.atom (.push a f)) (.atom (.push b g)))

theorem fanScan_run (src a b : K) (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (f g : Bool → Bool) (l x y : List Bool) (s : Store K Bool) :
    ∃ q, (fanScan src a b f g).Exec (((s.put src l).put a x).put b y) (3*l.length+1)
      ((((s.put src []).put a (l.reverse.map f ++ x)).put b (l.reverse.map g ++ y)).flag q) := by
  induction l generalizing x y s with
  | nil =>
    refine ⟨s.state,?_⟩
    simpa [Store.put,Store.flag] using (Exec.scan_nil
      (c := .seq (.atom (.push a f)) (.atom (.push b g))) (f := fun _ x => x)
      (s := ((s.put src []).put a x).put b y) (by simp [hsa,hsb]))
  | cons v l ih =>
    obtain ⟨q,hq⟩ := ih (f v :: x) (g v :: y) (s.flag v)
    refine ⟨q,?_⟩
    have hbody : (.seq (.atom (.push a f)) (.atom (.push b g)) : Code K Bool).Exec
        ⟨v,Function.update ((((s.put src (v::l)).put a x).put b y).tape) src l⟩ (1+1)
        ((((s.flag v).put src l).put a (f v::x)).put b (g v::y)) := by
      convert Exec.seq (Exec.atom (.push a f) _) (Exec.atom (.push b g) _) using 1
      refine Store.ext _ _ ?_ ?_
      · rfl
      funext k
      by_cases h0 : k=src <;> by_cases h1 : k=a <;> by_cases h2 : k=b <;>
        simp_all [Prim.run,Store.put,Store.flag,Function.update_apply]
    have h := Exec.scan_cons (k := src) (f := fun _ v => v)
      (c := .seq (.atom (.push a f)) (.atom (.push b g)))
      (s := ((s.put src (v::l)).put a x).put b y) (b := v) (rest := l)
      (by simp [hsa,hsb]) hbody hq
    convert h using 1 <;> simp [List.reverse_cons,List.append_assoc]; omega

@[reducible] def copyMap (src dst tmp : K) (f : Bool → Bool) : Code K Bool :=
  .seq (transfer src tmp) (.seq (fanScan tmp src dst id f) reset)

theorem copyMap_run (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (f : Bool → Bool) (s : Store K Bool) (ht : s.tape tmp = []) :
    (copyMap src dst tmp f).Exec s (5*(s.tape src).length+4)
      ((s.put dst ((s.tape src).map f ++ s.tape dst)).flag false) := by
  have h1 := transfer_run src tmp hst s
  rw [ht,List.append_nil] at h1
  obtain ⟨q,h2⟩ := fanScan_run tmp src dst (Ne.symm hst) (Ne.symm hdt) hsd id f
    (s.tape src).reverse [] (s.tape dst) (s.flag false)
  have heq : ((((s.flag false).put tmp (s.tape src).reverse).put src []).put dst (s.tape dst)) =
      (((s.put src []).put tmp (s.tape src).reverse).flag false) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases h0 : k=src <;> by_cases h1 : k=dst <;> by_cases h2 : k=tmp <;>
      simp_all [Store.put,Store.flag]
  rw [heq] at h2
  have h3 := Exec.seq h1 (Exec.seq h2 (reset_run _))
  have hend : (((((s.flag false).put tmp []).put src
      ((s.tape src).reverse.reverse.map id ++ [])).put dst
      ((s.tape src).reverse.reverse.map f ++ s.tape dst)).flag q).flag false =
      (s.put dst ((s.tape src).map f ++ s.tape dst)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases h0 : k=src <;> by_cases h1 : k=dst <;> by_cases h2 : k=tmp <;>
      simp_all [Store.put,Store.flag]
  rw [hend] at h3
  convert h3 using 1; simp; omega

@[reducible] def copy (src dst tmp : K) : Code K Bool := copyMap src dst tmp id
@[reducible] def count (src dst tmp : K) : Code K Bool := copyMap src dst tmp (fun _ => true)

theorem copy_run (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : Store K Bool) (ht : s.tape tmp = []) :
    (copy src dst tmp).Exec s (5*(s.tape src).length+4)
      ((s.put dst (s.tape src ++ s.tape dst)).flag false) := by
  simpa using copyMap_run src dst tmp hsd hst hdt id s ht

theorem count_run (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : Store K Bool) (ht : s.tape tmp = []) :
    (count src dst tmp).Exec s (5*(s.tape src).length+4)
      ((s.put dst (List.replicate (s.tape src).length true ++ s.tape dst)).flag false) := by
  simpa using copyMap_run src dst tmp hsd hst hdt (fun _ => true) s ht

end Ops
end DirectedFeedback.StackDSL


namespace DirectedFeedback.StackDSL
open Code
variable {K : Type} [DecidableEq K]
namespace Ops

theorem scan_indexed (counter : K) (c : Code K Bool) (n : Nat)
    (states : Nat → Store K Bool) (cost : Nat → Nat)
    (hc : ∀ i, i ≤ n → (states i).tape counter = List.replicate (n-i) true)
    (hb : ∀ i, i < n → c.Exec ((states i).put counter (List.replicate (n-(i+1)) true))
      (cost i) (states (i+1))) :
    (Code.scan counter (fun s _ => s) c).Exec (states 0)
      (n+1+∑ i ∈ Finset.range n, cost i) (states n) := by
  induction n generalizing states cost with
  | zero =>
    simpa using (Exec.scan_nil (c := c) (f := fun s _ => s) (s := states 0)
      (by simpa using hc 0 (by omega)))
  | succ n ih =>
    have hh := ih (fun i => states (i+1)) (fun i => cost (i+1))
      (by intro i hi; simpa [Nat.add_sub_add_right] using hc (i+1) (by omega))
      (by intro i hi; simpa [Nat.add_assoc] using hb (i+1) (by omega))
    have h := Exec.scan_cons (k := counter) (f := fun s _ => s) (c := c)
      (s := states 0) (b := true) (rest := List.replicate n true)
      (by simpa [List.replicate_succ] using hc 0 (by omega))
      (by simpa [Store.put] using hb 0 (by omega)) hh
    convert h using 1
    rw [Finset.sum_range_succ']
    omega

@[reducible] def pushN (k : K) : Nat → Code K Bool
  | 0 => reset
  | n+1 => .seq (push k true) (pushN k n)

theorem pushN_run (k : K) (n : Nat) (s : Store K Bool) :
    (pushN k n).Exec s (n+1)
      ((s.put k (List.replicate n true ++ s.tape k)).flag false) := by
  induction n generalizing s with
  | zero => simpa using reset_run s
  | succ n ih =>
    have h := Exec.seq (push_run s k true) (ih (s.put k (true::s.tape k)))
    convert h using 1 <;> first | omega | simp [List.replicate_succ',List.append_assoc]

theorem subtract_run (src counter : K) (hne : src ≠ counter) (a b : Nat) (s : Store K Bool) :
    (Code.scan counter (fun s _ => s) (pop src)).Exec
      ((s.put src (List.replicate a true)).put counter (List.replicate b true))
      (2*b+1) ((s.put src (List.replicate (a-b) true)).put counter []) := by
  let states := fun i => (s.put src (List.replicate (a-i) true)).put counter (List.replicate (b-i) true)
  have h := scan_indexed counter (pop src) b states (fun _ => 1)
    (by intro i hi; simp [states]) (by
      intro i hi
      convert pop_run ((states i).put counter (List.replicate (b-(i+1)) true)) src using 1
      refine Store.ext _ _ rfl ?_
      funext k
      by_cases hs : k=src <;> by_cases hc : k=counter <;>
        simp_all [states,Store.put,List.tail_replicate]
      omega)
  convert h using 1 <;> simp [states]; omega

theorem drop_run (src counter : K) (hne : src ≠ counter) (l : List Bool) (b : Nat) (s : Store K Bool) :
    (Code.scan counter (fun s _ => s) (pop src)).Exec
      ((s.put src l).put counter (List.replicate b true))
      (2*b+1) ((s.put src (l.drop b)).put counter []) := by
  let states := fun i => (s.put src (l.drop i)).put counter (List.replicate (b-i) true)
  have h := scan_indexed counter (pop src) b states (fun _ => 1)
    (by intro i hi; simp [states]) (by
      intro i hi
      convert pop_run ((states i).put counter (List.replicate (b-(i+1)) true)) src using 1
      refine Store.ext _ _ rfl ?_
      funext k
      by_cases hs : k=src <;> by_cases hc : k=counter <;>
        simp_all [states,Store.put])
  convert h using 1 <;> simp [states]; omega

end Ops
end DirectedFeedback.StackDSL


namespace DirectedFeedback.BoundedExpr
open scoped BigOperators

inductive Expr : Nat → Type
  | lit {r : Nat} (value : Nat) : Expr r
  | arg {r : Nat} (index : Fin r) : Expr r
  | length {r : Nat} : Expr r
  | bit {r : Nat} (index : Expr r) : Expr r
  | add {r : Nat} (a b : Expr r) : Expr r
  | mul {r : Nat} (a b : Expr r) : Expr r
  | sub {r : Nat} (a b : Expr r) : Expr r
  | zero {r : Nat} (a : Expr r) : Expr r
  | sum {r : Nat} (bound : Expr r) (body : Expr (r+1)) : Expr r

namespace Expr

def eval {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat) : Nat :=
  match e with
  | .lit n => n
  | .arg i => args i
  | .length => input.length
  | .bit i => if input[i.eval input args]?.getD false then 1 else 0
  | .add a b => a.eval input args + b.eval input args
  | .mul a b => a.eval input args * b.eval input args
  | .sub a b => a.eval input args - b.eval input args
  | .zero a => if a.eval input args = 0 then 1 else 0
  | .sum b e => ∑ i ∈ Finset.range (b.eval input args), e.eval input (Fin.cons i args)

noncomputable def bound {r : Nat} : Expr r → Polynomial Nat
  | .lit n => Polynomial.C n
  | .arg _ | .length => Polynomial.X
  | .bit _ | .zero _ => 1
  | .add a b => a.bound + b.bound
  | .mul a b => a.bound * b.bound
  | .sub a _ => a.bound
  | .sum b e => b.bound * e.bound.comp (Polynomial.X + b.bound)

theorem polynomial_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

theorem eval_le_bound {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : input.length ≤ n) (ha : ∀ i, args i ≤ n) : e.eval input args ≤ e.bound.eval n := by
  induction e generalizing input n with
  | lit k => simp [eval,bound]
  | arg i => simpa [eval,bound] using ha i
  | length => simpa [eval,bound] using hi
  | bit i ih => simp only [eval,bound,Polynomial.eval_one]; split <;> omega
  | add a b iha ihb =>
    simpa only [eval,bound,Polynomial.eval_add] using
      Nat.add_le_add (iha input args n hi ha) (ihb input args n hi ha)
  | mul a b iha ihb =>
    simpa only [eval,bound,Polynomial.eval_mul] using
      Nat.mul_le_mul (iha input args n hi ha) (ihb input args n hi ha)
  | sub a b iha ihb => exact (Nat.sub_le ..).trans (iha input args n hi ha)
  | zero a iha => simp only [eval,bound,Polynomial.eval_one]; split <;> omega
  | @sum r b e ihb ihe =>
    have hb := ihb input args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval input args),
        e.eval input (Fin.cons i args) ≤ e.bound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval input args := Finset.mem_range.mp hm
      apply ihe input (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    simp only [eval,bound,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X]
    calc
      _ ≤ ∑ _i ∈ Finset.range (b.eval input args), e.bound.eval (n+b.bound.eval n) :=
        Finset.sum_le_sum heach
      _ = b.eval input args * e.bound.eval (n+b.bound.eval n) := by simp
      _ ≤ b.bound.eval n * e.bound.eval (n+b.bound.eval n) := Nat.mul_le_mul_right _ hb

end Expr
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

namespace Expr

@[reducible] def compile {r : Nat} (e : Expr r) (input : Nat) (args : Fin r → Nat)
    (out fresh : Nat) : Code Nat Bool :=
  match e with
  | .lit n => pushN out n
  | .arg i => copy (args i) out fresh
  | .length => count input out fresh
  | .add a b => .seq (a.compile input args out fresh) (b.compile input args out fresh)
  | .mul a b =>
    .seq (a.compile input args fresh (fresh+2))
      (.seq (b.compile input args (fresh+1) (fresh+2))
        (.seq (.scan fresh (fun s _ => s) (copy (fresh+1) out (fresh+2))) (clear (fresh+1))))
  | .sub a b =>
    .seq (a.compile input args fresh (fresh+2))
      (.seq (b.compile input args (fresh+1) (fresh+2))
        (.seq (.scan (fresh+1) (fun s _ => s) (pop fresh)) (transfer fresh out)))
  | .zero a =>
    .seq (a.compile input args fresh (fresh+1))
      (.seq (.atom (.peek fresh (fun _ x => x.isNone)))
        (.seq (clear fresh) (.seq (.branch id (push out true) idle) reset)))
  | .bit i =>
    .seq (i.compile input args fresh (fresh+1))
      (.seq (copy input (fresh+1) (fresh+2))
        (.seq (.scan fresh (fun s _ => s) (pop (fresh+1)))
          (.seq (.atom (.peek (fresh+1) (fun _ x => x.getD false)))
            (.seq (clear (fresh+1)) (.seq (.branch id (push out true) idle) reset)))))
  | .sum b e =>
    .seq (b.compile input args fresh (fresh+2))
      (.seq (.scan fresh (fun s _ => s)
        (.seq (e.compile input (Fin.cons (fresh+1) args) out (fresh+2)) (push (fresh+1) true)))
        (clear (fresh+1)))

def cost {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat) : Nat :=
  match e with
  | .lit n => n+1
  | .arg i => 5*args i+4
  | .length => 5*input.length+4
  | .add a b => a.cost input args + b.cost input args
  | .mul a b => a.cost input args + b.cost input args +
      a.eval input args * (5*b.eval input args+5) + 2*b.eval input args+2
  | .sub a b => a.cost input args + b.cost input args +
      2*b.eval input args + 2*(a.eval input args-b.eval input args)+3
  | .zero a => a.cost input args + 2*a.eval input args+5
  | .bit i => i.cost input args + 5*input.length + 2*i.eval input args +
      2*(input.length-i.eval input args)+10
  | .sum b e => b.cost input args +
      (∑ i ∈ Finset.range (b.eval input args), e.cost input (Fin.cons i args))+4*b.eval input args+2

noncomputable def costBound {r : Nat} : Expr r → Polynomial Nat
  | .lit n => Polynomial.C (n+1)
  | .arg _ | .length => 5*Polynomial.X+4
  | .add a b => a.costBound+b.costBound
  | .mul a b => a.costBound+b.costBound+a.bound*(5*b.bound+5)+2*b.bound+2
  | .sub a b => a.costBound+b.costBound+2*b.bound+2*a.bound+3
  | .zero a => a.costBound+2*a.bound+5
  | .bit i => i.costBound+7*Polynomial.X+2*i.bound+10
  | .sum b e => b.costBound+b.bound*e.costBound.comp (Polynomial.X+b.bound)+4*b.bound+2

theorem cost_le_bound {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : input.length ≤ n) (ha : ∀ i, args i ≤ n) : e.cost input args ≤ e.costBound.eval n := by
  induction e generalizing input n with
  | lit k => simp [cost,costBound]
  | arg i =>
    have hai := ha i
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X]; omega
  | length => simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X]; omega
  | add a b iha ihb =>
    simpa [cost,costBound] using Nat.add_le_add (iha input args n hi ha) (ihb input args n hi ha)
  | mul a b iha ihb =>
    have h1 := iha input args n hi ha
    have h2 := ihb input args n hi ha
    have h3 := a.eval_le_bound input args n hi ha
    have h4 := b.eval_le_bound input args n hi ha
    have hm := Nat.mul_le_mul h3 (Nat.add_le_add_right (Nat.mul_le_mul_left 5 h4) 5)
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  | sub a b iha ihb =>
    have h1 := iha input args n hi ha
    have h2 := ihb input args n hi ha
    have h3 := a.eval_le_bound input args n hi ha
    have h4 := b.eval_le_bound input args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  | zero a iha =>
    have h1 := iha input args n hi ha
    have h2 := a.eval_le_bound input args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  | bit i ih =>
    have h1 := ih input args n hi ha
    have h2 := i.eval_le_bound input args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  | @sum r b e ihb ihe =>
    have hb := b.eval_le_bound input args n hi ha
    have hbc := ihb input args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval input args),
        e.cost input (Fin.cons i args) ≤ e.costBound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval input args := Finset.mem_range.mp hm
      apply ihe input (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    have hsum : (∑ i ∈ Finset.range (b.eval input args), e.cost input (Fin.cons i args)) ≤
        b.bound.eval n * e.costBound.eval (n+b.bound.eval n) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (b.eval input args), e.costBound.eval (n+b.bound.eval n) :=
          Finset.sum_le_sum heach
        _ = b.eval input args * e.costBound.eval (n+b.bound.eval n) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hb
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp,Polynomial.eval_X]
    omega

end Expr
end DirectedFeedback.BoundedExpr

end OAI
