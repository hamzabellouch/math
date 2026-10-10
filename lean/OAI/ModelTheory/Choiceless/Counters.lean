import OAI.ModelTheory.Choiceless.GaussMachine

namespace OAI

namespace CPTSeparation.CounterLang

section

open StackLang StackLang.Macros

inductive Reg (R : Type) where
 | reg : R → Reg R
 | input | output | work | back | count
 deriving DecidableEq, Fintype

structure Data (R : Type) where
 regs : R → List Letter
 input : List Letter := []
 output : List Letter := []
 work : List Letter := []
 back : List Letter := []
 count : List Letter := []

namespace Data

variable {R : Type} [DecidableEq R]

def tapes (d : Data R) : Reg R → List Letter
 | .reg r => d.regs r
 | .input => d.input
 | .output => d.output
 | .work => d.work
 | .back => d.back
 | .count => d.count

@[simp] lemma tapes_reg (d : Data R) (r : R) (xs : List Letter) :
 Function.update d.tapes (.reg r) xs = ({d with regs := Function.update d.regs r xs}).tapes := by
 funext k; cases k with
 | reg k => simp [tapes,Function.update]
 | _ => simp [tapes,Function.update]

@[simp] lemma tapes_input (d : Data R) (xs : List Letter) : Function.update d.tapes .input xs = ({d with input := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_output (d : Data R) (xs : List Letter) : Function.update d.tapes .output xs = ({d with output := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_work (d : Data R) (xs : List Letter) : Function.update d.tapes .work xs = ({d with work := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_back (d : Data R) (xs : List Letter) : Function.update d.tapes .back xs = ({d with back := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_count (d : Data R) (xs : List Letter) : Function.update d.tapes .count xs = ({d with count := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

end Data

structure State (R σ : Type) where
 ctl : σ
 nums : R → ℕ
 input : List Letter
 output : List Letter

variable {R σ : Type} [DecidableEq R]

def unary (ns : R → ℕ) : R → List Letter := fun r => List.replicate (ns r) none

@[simp] lemma unary_update (ns : R → ℕ) (i : R) (n : ℕ) :
 unary (Function.update ns i n) = Function.update (unary ns) i (List.replicate n none) := by
 funext r; by_cases h : r = i <;> simp [unary,Function.update,h]

def State.data (s : State R σ) : Data R := ⟨unary s.nums,s.input,s.output,[],[],[]⟩

def State.encode (s : State R σ) : SStore (Reg R) Letter σ := state s.ctl none s.data.tapes

inductive Atom (R σ : Type) where
 | load (f : σ → σ)
 | zero (r : R)
 | inc (r : R)
 | dec (r : R)
 | positive (r : R) (f : σ → Bool → σ)
 | copy (r s : R) (h : r ≠ s)
 | add (r s : R) (h : r ≠ s)
 | lookup (r : R) (f : σ → Option Letter → σ)
 | consume (f : σ → Option Letter → σ)
 | emit (f : σ → Letter)

namespace Atom

def eval : Atom R σ → State R σ → State R σ
 | .load f,s => {s with ctl := f s.ctl}
 | .zero r,s => {s with nums := Function.update s.nums r 0}
 | .inc r,s => {s with nums := Function.update s.nums r (s.nums r+1)}
 | .dec r,s => {s with nums := Function.update s.nums r (s.nums r-1)}
 | .positive r f,s => {s with ctl := f s.ctl (s.nums r != 0)}
 | .copy r t _,s => {s with nums := Function.update s.nums t (s.nums r)}
 | .add r t _,s => {s with nums := Function.update s.nums t (s.nums r+s.nums t)}
 | .lookup r f,s => {s with ctl := f s.ctl s.input[s.nums r]?}
 | .consume f,s => {s with ctl := f s.ctl s.input.head?, input := s.input.tail}
 | .emit f,s => {s with output := f s.ctl :: s.output}

def cost : Atom R σ → State R σ → ℕ
 | .zero r,s => 2*s.nums r+3
 | .copy r t _,s => 2*s.nums t+4*s.nums r+12
 | .add r _ _,s => 4*s.nums r+7
 | .lookup r _,s => 10*(s.nums r+s.input.length+1)+30
 | _,_ => 1

end Atom

inductive Program (R σ : Type) where
 | atom (a : Atom R σ)
 | seq (a b : Program R σ)
 | cond (f : σ → Bool) (a b : Program R σ)
 | loop (f : σ → Bool) (a : Program R σ)

inductive Runs : Program R σ → State R σ → State R σ → ℕ → Prop
 | atom (a : Atom R σ) (s : State R σ) : Runs (.atom a) s (a.eval s) (a.cost s)
 | seq {a b s t u m n} : Runs a s t m → Runs b t u n → Runs (.seq a b) s u (1+(m+n))
 | cond_true {f a b s t n} : f s.ctl = true → Runs a s t n → Runs (.cond f a b) s t (1+n)
 | cond_false {f a b s t n} : f s.ctl = false → Runs b s t n → Runs (.cond f a b) s t (1+n)
 | loop_false {f a s} : f s.ctl = false → Runs (.loop f a) s s 1
 | loop_true {f a s t u m n} : f s.ctl = true → Runs a s t m → Runs (.loop f a) t u n →
     Runs (.loop f a) s u (1+(m+n))
 | mono {a s t m n} : Runs a s t m → m ≤ n → Runs a s t n

lemma Runs.loop_steps {f : σ → Bool} {p : Program R σ} (states : ℕ → State R σ) (n b : ℕ)
    (guard : ∀ i < n, f (states i).ctl = true) (stop : f (states n).ctl = false)
    (step : ∀ i < n, Runs p (states i) (states (i+1)) b) :
    Runs (.loop f p) (states 0) (states n) ((b+1)*n+1) := by
 induction n generalizing states with
 | zero => simpa using Runs.loop_false stop
 | succ n ih =>
   have h := Runs.loop_true (guard 0 (by omega)) (step 0 (by omega))
     (ih (fun i => states (i+1)) (fun i hi => guard (i+1) (by omega)) stop
       (fun i hi => step (i+1) (by omega)))
   convert h using 1 ; first | rfl | ring

end

section

open StackLang StackLang.Macros

variable {R σ : Type} [decidableR : DecidableEq R]

abbrev LowProgram (R σ : Type) := SProgram (Reg R) Letter σ

def skipBody : LowProgram R σ := .atom
 (.pop .count (fun c _ => c) (.pop .work (fun c _ => c)
  (.peek .count (fun c a => (a,c.2)) .done)))

def skipLoop : LowProgram R σ := .loop (fun c => c.1.isSome) skipBody

def lookup (r : R) (f : σ → Option Letter → σ) : LowProgram R σ :=
 .seq (copy .input .work .back)
 (.seq (copy (.reg r) .count .back)
 (.seq (peek .count)
 (.seq skipLoop
 (.seq (.atom (.peek .work (fun c a => (none,f c.2 a)) .done)) (clear .work)))))

namespace Atom

def compile : Atom R σ → LowProgram R σ
 | .load f => .atom (.load (fun c => (none,f c.2)) .done)
 | .zero r => clear (.reg r)
 | .inc r => .atom (.push (.reg r) (fun _ => none) .done)
 | .dec r => .atom (.pop (.reg r) (fun c _ => c) .done)
 | .positive r f => .atom (.peek (.reg r) (fun c a => (none,f c.2 a.isSome)) .done)
 | .copy r t _ => .seq (clear (.reg t)) (StackLang.Macros.copy (.reg r) (.reg t) .back)
 | .add r t _ => StackLang.Macros.copy (.reg r) (.reg t) .back
 | .lookup r f => CounterLang.lookup r f
 | .consume f => .atom (.pop .input (fun c a => (none,f c.2 a)) .done)
 | .emit f => .atom (.push .output (fun c => f c.2) .done)

end Atom

@[simp] lemma unary_update_self (ns : R → ℕ) (r : R) :
 Function.update (unary ns) r (List.replicate (ns r) none) = unary ns :=
  Function.update_eq_self r (unary ns)

omit R in
lemma unary_length
    {R : Type}
    [DecidableEq R] (s : R → ℕ) (r : R) : (unary s r).length = s r := by simp [unary]

@[simp] lemma unary_head (n : ℕ) : (List.replicate n (none : Letter)).head?.isSome = (n != 0) := by
 cases n <;> rfl

lemma skipLoop_runs (v : σ) (d : Data R) (k : ℕ) (xs : List Letter) :
 StackLang.Runs skipLoop
   (state v (List.replicate k (none : Letter)).head? ({d with count := List.replicate k none,work := xs}).tapes)
   (state v none ({d with count := [],work := xs.drop k}).tapes) (2*k+1) := by
 induction k generalizing xs with
 | zero => simpa [skipLoop] using
     (StackLang.Runs.loop_false (b := skipBody) (f := fun c : Option Letter × σ => c.1.isSome)
       (s := state v none ({d with count := [],work := xs}).tapes) rfl)
 | succ k ih =>
   have hb : StackLang.Runs skipBody
       (state v (some none) ({d with count := List.replicate (k+1) none,work := xs}).tapes)
       (state v (List.replicate k (none : Letter)).head?
         ({d with count := List.replicate k none,work := xs.tail}).tapes) 1 := by
     apply StackLang.Runs.atom_of
     simp [Action.run,state,Data.tapes,List.replicate_succ]
   have h := StackLang.Runs.loop_true (f := fun c : Option Letter × σ => c.1.isSome) rfl hb (ih xs.tail)
   convert h using 1 <;> first | rfl | omega | simp [List.drop_tail]

lemma lookup_runs (r : R) (f : σ → Option Letter → σ) (s : State R σ) :
 StackLang.Runs (lookup r f) s.encode ((Atom.lookup r f).eval s).encode
   ((Atom.lookup r f).cost s) := by
 let d := s.data
 have hc₁ := copy_runs (.input : Reg R) .work .back (by simp) (by simp) (by simp)
     s.ctl none d.tapes s.input []
 have hc₂ := copy_runs (.reg r) (.count : Reg R) .back (by simp) (by simp) (by simp)
     s.ctl none ({d with work := s.input}).tapes (List.replicate (s.nums r) none) []
 have hp : StackLang.Runs (peek (.count : Reg R))
     (state s.ctl none ({d with work := s.input,count := List.replicate (s.nums r) none}).tapes)
     (state s.ctl (List.replicate (s.nums r) (none : Letter)).head?
       ({d with work := s.input,count := List.replicate (s.nums r) none}).tapes) 1 := by
   apply StackLang.Runs.atom_of
   rfl
 have hs := skipLoop_runs s.ctl d (s.nums r) s.input
 have he : StackLang.Runs
     (.atom (.peek (.work : Reg R) (fun c a => (none,f c.2 a)) .done))
     (state s.ctl none ({d with work := s.input.drop (s.nums r),count := []}).tapes)
     (state (f s.ctl s.input[s.nums r]?) none
       ({d with work := s.input.drop (s.nums r),count := []}).tapes) 1 := by
   apply StackLang.Runs.atom_of
   simp [Action.run,state,Data.tapes]
 have hcl := clear_runs (.work : Reg R) (f s.ctl s.input[s.nums r]?) none
     ({d with count := []}).tapes (s.input.drop (s.nums r))
 have hc₁' : StackLang.Runs (copy (.input : Reg R) .work .back) s.encode
     (state s.ctl none ({d with work := s.input}).tapes) (4*s.input.length+7) := by
   simpa [d,State.encode,State.data] using hc₁
 have hc₂' : StackLang.Runs (copy (.reg r) (.count : Reg R) .back)
     (state s.ctl none ({d with work := s.input}).tapes)
     (state s.ctl none ({d with work := s.input,count := List.replicate (s.nums r) none}).tapes)
     (4*s.nums r+7) := by
   simpa [d,State.data] using hc₂
 have hcl' : StackLang.Runs (clear (.work : Reg R))
     (state (f s.ctl s.input[s.nums r]?) none ({d with work := s.input.drop (s.nums r),count := []}).tapes)
     ((Atom.lookup r f).eval s).encode (2*(s.input.drop (s.nums r)).length+3) := by
   simpa [d,State.encode,State.data,Atom.eval] using hcl
 have h := hc₁'.seq (hc₂'.seq (hp.seq (hs.seq (he.seq hcl'))))
 exact h.mono (by simp only [Atom.cost,List.length_drop]; omega)

lemma Atom.zero_runs (r : R) (s : State R σ) :
 StackLang.Runs (Atom.compile (.zero r)) s.encode ((Atom.zero r).eval s).encode ((Atom.zero r).cost s) := by
 have h := clear_runs (.reg r) s.ctl none s.data.tapes (List.replicate (s.nums r) none)
 simpa [compile,State.encode,State.data,eval,cost,unary_update] using h

lemma Atom.add_runs (r t : R) (hrt : r ≠ t) (s : State R σ) :
 StackLang.Runs (Atom.compile (.add r t hrt)) s.encode ((Atom.add r t hrt).eval s).encode
   ((Atom.add r t hrt).cost s) := by
 have h := copy_runs (.reg r) (.reg t) (.back : Reg R) (by simpa) (by simp) (by simp)
     s.ctl none s.data.tapes (List.replicate (s.nums r) none) (List.replicate (s.nums t) none)
 simpa [compile,State.encode,State.data,eval,cost,unary_update,← List.replicate_add] using h

lemma Atom.compile_runs (a : Atom R σ) (s : State R σ) :
 StackLang.Runs a.compile s.encode (a.eval s).encode (a.cost s) := by
 cases a with
 | load f =>
   apply StackLang.Runs.atom_of
   rfl
 | zero r => exact zero_runs r s
 | inc r =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,eval,state,Data.tapes,unary_update,List.replicate_succ,unary]
 | dec r =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,eval,state,Data.tapes,unary_update,unary]
 | positive r f =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,state,Data.tapes,eval,unary]
 | consume f =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,state,Data.tapes,eval]
 | emit f =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,state,Data.tapes,eval]
 | add r t hrt => exact add_runs r t hrt s
 | copy r t hrt =>
   have hz := zero_runs t s
   have ha := add_runs r t hrt ((Atom.zero t).eval s)
   have h := hz.seq ha
   have h' : StackLang.Runs (Atom.compile (.copy r t hrt)) s.encode
       ((Atom.copy r t hrt).eval s).encode (1+(2*s.nums t+3+(4*s.nums r+7))) := by
     simpa only [compile,eval,cost,Function.update_self,Function.update_of_ne hrt,
       Nat.add_zero,Function.update_idem] using h
   exact h'.mono (by simp only [cost]; omega)
 | lookup r f => exact lookup_runs r f s

namespace Program

def compile : Program R σ → LowProgram R σ
 | .atom a => a.compile
 | .seq a b => .seq a.compile b.compile
 | .cond f a b => .cond (fun c => f c.2) a.compile b.compile
 | .loop f a => .loop (fun c => f c.2) a.compile

end Program

lemma Runs.compiles {p : Program R σ} {s t : State R σ} {n : ℕ} (h : Runs p s t n) :
 StackLang.Runs p.compile s.encode t.encode n := by
 induction h with
 | atom a s => exact a.compile_runs s
 | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
 | cond_true hf _ ih => exact StackLang.Runs.cond_true hf ih
 | cond_false hf _ ih => exact StackLang.Runs.cond_false hf ih
 | loop_false hf => exact StackLang.Runs.loop_false hf
 | loop_true hf _ _ ih₁ ih₂ => exact StackLang.Runs.loop_true hf ih₁ ih₂
 | mono _ h ih => exact ih.mono h

end

section

variable {R V : Type} [decidableR : DecidableEq R]

omit R V in
@[ext] lemma State.ext
    {R : Type}
    {V : Type}
    [DecidableEq R] {s t : State R V} (hc : s.ctl = t.ctl) (hn : s.nums = t.nums)
   (hi : s.input = t.input) (ho : s.output = t.output) : s = t := by
 cases s; cases t; simp_all

lemma Runs.atom_of {a : Atom R V} {s t : State R V} {n : ℕ}
    (he : a.eval s = t) (hn : a.cost s ≤ n) : Runs (.atom a) s t n := by
 subst t
 exact (Runs.atom a s).mono hn

@[simp] lemma bne_nat_zero (n : ℕ) : (n != 0) = decide (0 < n) := by
 cases n <;> rfl

def testPos (r : R) : Program R (Bool × V) := .atom (.positive r (fun c b => (b,c.2)))

def flag (s : State R (Bool × V)) (b : Bool) : State R (Bool × V) := {s with ctl := (b,s.ctl.2)}

def mulBody (a dst tmp : R) (had : a ≠ dst) : Program R (Bool × V) :=
 .seq (.atom (.add a dst had)) (.seq (.atom (.dec tmp)) (testPos tmp))

def mulLoop (a dst tmp : R) (had : a ≠ dst) : Program R (Bool × V) :=
 .loop Prod.fst (mulBody a dst tmp had)

def multiply (a b dst tmp : R) (had : a ≠ dst) (hbt : b ≠ tmp) : Program R (Bool × V) :=
 .seq (.atom (.zero dst)) (.seq (.atom (.copy b tmp hbt))
   (.seq (testPos tmp) (mulLoop a dst tmp had)))

def mulState (s : State R (Bool × V)) (dst tmp : R) (A B i : ℕ) : State R (Bool × V) :=
 {s with ctl := (decide (i < B),s.ctl.2), nums := Function.update (Function.update s.nums dst (A*i)) tmp (B-i)}

lemma mulBody_runs (a dst tmp : R) (had : a ≠ dst) (hat : a ≠ tmp) (hdt : dst ≠ tmp)
   (s : State R (Bool × V)) (B i : ℕ) (hi : i < B) :
 Runs (mulBody a dst tmp had) (mulState s dst tmp (s.nums a) B i)
   (mulState s dst tmp (s.nums a) B (i+1)) (4*s.nums a+11) := by
 let s₀ := mulState s dst tmp (s.nums a) B i
 let s₁ := (Atom.add a dst had).eval s₀
 let s₂ := (Atom.dec tmp).eval s₁
 have h := (Runs.atom (.add a dst had) s₀).seq
   ((Runs.atom (.dec tmp) s₁).seq (Runs.atom (.positive tmp (fun c b => (b,c.2))) s₂))
 have he : (Atom.positive tmp (fun (c : Bool × V) b => (b,c.2))).eval s₂ =
     mulState s dst tmp (s.nums a) B (i+1) := by
   apply State.ext
   · have hb : 0 < B-i-1 ↔ i+1 < B := by omega
     simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,Ne.symm hdt,bne_nat_zero,hb]
   · funext k
     by_cases hk : k = tmp
     · subst k; simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,hdt,Ne.symm hdt]; omega
     · by_cases hk' : k = dst
       · subst k
         simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,hdt,hat,had,Ne.symm hdt]
         ring
       · simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,hk,hk']
   · rfl
   · rfl
 rw [he] at h
 exact h.mono (by simp [s₀,mulState,Atom.cost,Function.update,hat,had]; omega)

lemma mulLoop_runs (a dst tmp : R) (had : a ≠ dst) (hat : a ≠ tmp) (hdt : dst ≠ tmp)
   (s : State R (Bool × V)) (B : ℕ) :
 Runs (mulLoop a dst tmp had) (mulState s dst tmp (s.nums a) B 0)
   (mulState s dst tmp (s.nums a) B B) ((4*s.nums a+12)*B+1) := by
 exact Runs.loop_steps (fun i => mulState s dst tmp (s.nums a) B i) B (4*s.nums a+11)
   (by intro i hi; simp [mulState,hi]) (by simp [mulState])
   (by intro i hi; exact mulBody_runs a dst tmp had hat hdt s B i hi)

lemma multiply_runs (a b dst tmp : R) (had : a ≠ dst) (hbt : b ≠ tmp)
   (hat : a ≠ tmp) (hbd : b ≠ dst) (hdt : dst ≠ tmp) (s : State R (Bool × V)) :
 Runs (multiply a b dst tmp had hbt) s
   {s with ctl := (false,s.ctl.2), nums := Function.update (Function.update s.nums dst (s.nums a*s.nums b)) tmp 0}
   (2*s.nums dst+2*s.nums tmp+4*s.nums b+(4*s.nums a+12)*s.nums b+20) := by
 let s₁ := (Atom.zero dst).eval s
 let s₂ := (Atom.copy b tmp hbt).eval s₁
 have he : (Atom.positive tmp (fun (c : Bool × V) b => (b,c.2))).eval s₂ =
     mulState s dst tmp (s.nums a) (s.nums b) 0 := by
   ext k <;> simp [s₂,s₁,Atom.eval,mulState,Function.update,hbd,bne_nat_zero]
 have hpre := (Runs.atom (.copy b tmp hbt) s₁).seq
    ((Runs.atom (.positive tmp (fun (c : Bool × V) b => (b,c.2))) s₂))
 have hp : Runs (.seq (.atom (.copy b tmp hbt)) (testPos tmp)) s₁
     (mulState s dst tmp (s.nums a) (s.nums b) 0) (2*s.nums tmp+4*s.nums b+14) := by
   rw [he] at hpre
   exact hpre.mono (by simp [s₁,Atom.cost,Atom.eval,Function.update,hbd,Ne.symm hdt]; omega)
 have hlo := mulLoop_runs a dst tmp had hat hdt s (s.nums b)
 have hf : mulState s dst tmp (s.nums a) (s.nums b) (s.nums b) =
     {s with ctl := (false,s.ctl.2), nums := Function.update (Function.update s.nums dst (s.nums a*s.nums b)) tmp 0} := by
   simp [mulState]
 rw [hf] at hlo
 have ht := (Runs.atom (.positive tmp (fun (c : Bool × V) b => (b,c.2))) s₂)
 rw [he] at ht
 have h := (Runs.atom (.zero dst) s).seq ((Runs.atom (.copy b tmp hbt) s₁).seq (ht.seq hlo))
 exact h.mono (by simp [s₁,Atom.cost,Atom.eval,Function.update,hbd,Ne.symm hdt]; omega)

def repeatAdd (src dst : R) (h : src ≠ dst) : ℕ → Program R V
 | 0 => .atom (.load id)
 | k+1 => .seq (.atom (.add src dst h)) (repeatAdd src dst h k)

lemma repeatAdd_runs (src dst : R) (hnd : src ≠ dst) (k : ℕ) (s : State R V) :
 Runs (repeatAdd src dst hnd k) s
   {s with nums := Function.update s.nums dst (s.nums dst+k*s.nums src)}
   ((4*s.nums src+8)*k+1) := by
 induction k generalizing s with
 | zero => simpa [repeatAdd,Atom.eval,Atom.cost] using Runs.atom (.load id) s
 | succ k ih =>
   have h := (Runs.atom (.add src dst hnd) s).seq (ih ((Atom.add src dst hnd).eval s))
   have he : (s.nums src+s.nums dst)+k*s.nums src = s.nums dst+(k+1)*s.nums src := by ring
   have h' : Runs (repeatAdd src dst hnd (k+1)) s
       {s with nums := Function.update s.nums dst (s.nums dst+(k+1)*s.nums src)}
       (1+(4*s.nums src+7+((4*s.nums src+8)*k+1))) := by
     simpa [repeatAdd,Atom.eval,Atom.cost,he,hnd] using h
   exact h'.mono (by nlinarith)

end

variable {R V : Type} [DecidableEq R]

def indexState (idx rem : R) (N i : ℕ) (s : State R (Bool × V)) : State R (Bool × V) :=
 {s with ctl := (decide (i<N),s.ctl.2), nums := Function.update (Function.update s.nums idx i) rem (N-i)}

def rangeBody (idx rem : R) (body : Program R (Bool × V)) : Program R (Bool × V) :=
 .seq body (.seq (.atom (.inc idx)) (.seq (.atom (.dec rem)) (testPos rem)))

def forRange (size idx rem : R) (hnr : size ≠ rem) (body : Program R (Bool × V)) : Program R (Bool × V) :=
 .seq (.atom (.copy size rem hnr)) (.seq (testPos rem)
   (.seq (.loop Prod.fst (rangeBody idx rem body)) (.atom (.zero idx))))

lemma rangeTail_runs (idx rem : R) (hir : idx ≠ rem) (N i : ℕ) (s : State R (Bool × V)) (hi : i<N) :
 Runs (.seq (.atom (.inc idx)) (.seq (.atom (.dec rem)) (testPos rem)))
   (flag (indexState idx rem N i s) false) (indexState idx rem N (i+1) s) 5 := by
 let s₀ := flag (indexState idx rem N i s) false
 let s₁ := (Atom.inc idx).eval s₀
 let s₂ := (Atom.dec rem).eval s₁
 have h := (Runs.atom (.inc idx) s₀).seq
   ((Runs.atom (.dec rem) s₁).seq (Runs.atom (.positive rem (fun c b => (b,c.2))) s₂))
 have he : (Atom.positive rem (fun (c : Bool × V) b => (b,c.2))).eval s₂ =
     indexState idx rem N (i+1) s := by
   have hh : 0 < N-i-1 ↔ i+1<N := by omega
   apply State.ext
   · simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,Ne.symm hir,bne_nat_zero,hh]
   · funext k
     by_cases hk : k = rem
     · subst k; simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,Ne.symm hir]; omega
     · by_cases hki : k = idx
       · subst k; simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,hir]
       · simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,hk,hki]
   · rfl
   · rfl
 rw [he] at h
 exact h

lemma forRange_runs (size idx rem : R) (hnr : size ≠ rem) (hir : idx ≠ rem)
   (body : Program R (Bool × V)) (S : ℕ → State R (Bool × V)) (N b : ℕ)
   (hsize : (S 0).nums size = N)
   (hi₀ : (S 0).nums idx = 0) (hr₀ : (S 0).nums rem = 0)
   (hiN : (S N).nums idx = 0) (hrN : (S N).nums rem = 0)
   (hcN : (S N).ctl.1 = false)
   (hb : ∀ i<N, Runs body (indexState idx rem N i (S i))
      (flag (indexState idx rem N i (S (i+1))) false) b) :
 Runs (forRange size idx rem hnr body) (S 0) (S N) ((b+13)*N+20) := by
 let inner := fun i => indexState idx rem N i (S i)
 have loop : Runs (.loop Prod.fst (rangeBody idx rem body)) (inner 0) (inner N) ((b+7)*N+1) := by
   apply Runs.loop_steps inner N (b+6)
   · intro i hi; simp [inner,indexState,hi]
   · simp [inner,indexState]
   · intro i hi
     have h := (hb i hi).seq (rangeTail_runs idx rem hir N i (S (i+1)) hi)
     convert h using 1 <;> first | rfl | omega
 have hz : Runs (.atom (.zero idx)) (inner N) (S N) (2*N+3) := by
   apply Runs.atom_of
   · apply State.ext
     · apply Prod.ext <;> simp [inner,indexState,Atom.eval,hcN]
     · funext k
       by_cases hki : k = idx
       · subst k; simp [inner,indexState,Atom.eval,Function.update,hiN]
       · by_cases hkr : k = rem
         · subst k; simp [inner,indexState,Atom.eval,Function.update,hrN,Ne.symm hir]
         · simp [inner,indexState,Atom.eval,Function.update,hki,hkr]
     · rfl
     · rfl
   · simp [inner,indexState,Atom.cost,Function.update,hir]
 let s₁ := (Atom.copy size rem hnr).eval (S 0)
 have ht : Runs (testPos rem) s₁ (inner 0) 1 := by
   apply Runs.atom_of
   · apply State.ext
     · simp [s₁,inner,indexState,Atom.eval,Function.update,hsize,bne_nat_zero]
     · funext k
       by_cases hkr : k = rem
       · subst k; simp [s₁,inner,indexState,Atom.eval,Function.update,hsize]
       · by_cases hki : k = idx
         · subst k; simp [s₁,inner,indexState,Atom.eval,Function.update,hi₀,hir]
         · simp [s₁,inner,indexState,Atom.eval,Function.update,hkr,hki]
     · rfl
     · rfl
   · rfl
 have h := (Runs.atom (.copy size rem hnr) (S 0)).seq (ht.seq (loop.seq hz))
 exact h.mono (by simp only [Atom.cost,hr₀,hsize]; nlinarith)

def bothPositive (a b : R) : Program R (Bool × V) :=
 .seq (testPos a) (.atom (.positive b (fun c q => (c.1 && q,c.2))))

def compareBody (a b : R) : Program R (Bool × V) :=
 .seq (.atom (.dec a)) (.seq (.atom (.dec b)) (bothPositive a b))

def compare (i j a b : R) (hia : i ≠ a) (hjb : j ≠ b)
    (f : V → Bool → V) : Program R (Bool × V) :=
 Program.seq (.atom (.copy i a hia)) <|
 Program.seq (.atom (.copy j b hjb)) <|
 Program.seq (bothPositive a b) <|
 Program.seq (.loop Prod.fst (compareBody a b)) <|
 Program.seq (testPos a) <|
 Program.seq (.atom (.positive b (fun c q => (c.1 || q,c.2))))
   (.atom (.load (fun c => (false,f c.2 (!c.1)))))

lemma bothPositive_runs (a b : R) (s : State R (Bool × V)) :
 Runs (bothPositive a b) s (flag s (decide (0<s.nums a ∧ 0<s.nums b))) 3 := by
 have h := (Runs.atom (.positive a (fun c q => (q,c.2))) s).seq
   (Runs.atom (.positive b (fun c q => (c.1 && q,c.2)))
     ((Atom.positive a (fun c q => (q,c.2))).eval s))
 simpa [bothPositive,testPos,Atom.eval,Atom.cost,flag,bne_nat_zero,Nat.pos_iff_ne_zero] using h

lemma compare_runs (i j a b : R) (hia : i ≠ a) (hjb : j ≠ b)
    (hja : j ≠ a) (hab : a ≠ b) (f : V → Bool → V) (s : State R (Bool × V)) :
 Runs (compare i j a b hia hjb f) s
   {s with ctl := (false,f s.ctl.2 (decide (s.nums i = s.nums j))), nums := Function.update (Function.update s.nums a (s.nums i - s.nums j)) b (s.nums j - s.nums i)}
   (2*s.nums a+2*s.nums b+20*(s.nums i+s.nums j)+40) := by
 let x := s.nums i
 let y := s.nums j
 let m := min x y
 let st (k : ℕ) : State R (Bool × V) :=
   {s with ctl := (decide (k < m),s.ctl.2), nums := Function.update (Function.update s.nums a (x-k)) b (y-k)}
 have guard (k : ℕ) : (0<x-k ∧ 0<y-k) ↔ k < m := by dsimp [m]; omega
 have hb (k : ℕ) (hk : k < m) : Runs (compareBody a b) (st k) (st (k+1)) 7 := by
   let s₁ := (Atom.dec a).eval (st k)
   let s₂ := (Atom.dec b).eval s₁
   have h := (Runs.atom (.dec a) (st k)).seq
      ((Runs.atom (.dec b) s₁).seq (bothPositive_runs a b s₂))
   have he : flag s₂ (decide (0<s₂.nums a ∧ 0<s₂.nums b)) = st (k+1) := by
     have hg : (0<x-k-1 ∧ 0<y-k-1) ↔ k+1 < m := by dsimp [m]; omega
     apply State.ext
     · apply Prod.ext
       · apply Bool.eq_iff_iff.mpr
         simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,Ne.symm hab]
         dsimp [m]; omega
       · rfl
     · funext r
       by_cases hra : r=a
       · subst r; simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,Ne.symm hab]; omega
       · by_cases hrb : r=b
         · subst r; simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,Ne.symm hab]; omega
         · simp [s₂,s₁,st,flag,Atom.eval,Function.update,hra,hrb]
     · rfl
     · rfl
   rw [he] at h
   exact h
 have hl : Runs (.loop Prod.fst (compareBody a b)) (st 0) (st m) (8*m+1) :=
   Runs.loop_steps st m 7 (by intro k hk; simp [st,hk]) (by simp [st]) hb
 let s₁ := (Atom.copy i a hia).eval s
 let s₂ := (Atom.copy j b hjb).eval s₁
 have hin : flag s₂ (decide (0<s₂.nums a ∧ 0<s₂.nums b)) = st 0 := by
   apply State.ext
   · apply Prod.ext
     · apply Bool.eq_iff_iff.mpr
       simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,hja,x,y,m]
     · rfl
   · funext r; simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,hja,x,y]
   · rfl
   · rfl
 have ht := bothPositive_runs a b s₂
 rw [hin] at ht
 let s₃ := (Atom.positive a (fun c q => (q,c.2))).eval (st m)
 let s₄ := (Atom.positive b (fun c q => (c.1 || q,c.2))).eval s₃
 have hend : (Atom.load (fun c : Bool × V => (false,f c.2 (!c.1)))).eval s₄ =
     {s with ctl := (false,f s.ctl.2 (decide (s.nums i = s.nums j))), nums := Function.update (Function.update s.nums a (s.nums i-s.nums j)) b (s.nums j-s.nums i)} := by
   have hx : x-m=x-y := by dsimp [m]; omega
   have hy : y-m=y-x := by dsimp [m]; omega
   have hz : (!decide (m<x) && !decide (m<y)) = decide (x=y) := by
     apply Bool.eq_iff_iff.mpr
     simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
     dsimp [m]; omega
   apply State.ext
   · simpa [s₄,s₃,st,Atom.eval,Function.update,hab,Ne.symm hab,x,y] using congrArg (fun z => (false,f s.ctl.2 z)) hz
   · simp [s₄,s₃,st,Atom.eval,hx,hy,x,y]
   · rfl
   · rfl
 have he := Runs.atom (.load (fun c : Bool × V => (false,f c.2 (!c.1)))) s₄
 rw [hend] at he
 have h := (Runs.atom (.copy i a hia) s).seq
   ((Runs.atom (.copy j b hjb) s₁).seq
   (ht.seq (hl.seq ((Runs.atom (.positive a (fun c q => (q,c.2))) (st m)).seq
   ((Runs.atom (.positive b (fun c q => (c.1 || q,c.2))) s₃).seq he)))))
 apply h.mono
 simp [s₁,Atom.cost,Atom.eval,Function.update,hja,Ne.symm hab]
 dsimp [x,y,m] at *
 omega

end CPTSeparation.CounterLang

end OAI
