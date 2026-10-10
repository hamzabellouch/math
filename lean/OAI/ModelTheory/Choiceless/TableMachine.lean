import OAI.ModelTheory.Choiceless.Counters

namespace OAI

namespace CPTSeparation.TableMachine

open CounterLang

inductive Index where
 | t | y | a | x | z
 deriving DecidableEq

instance : Fintype Index := ⟨{.t,.y,.a,.x,.z}, by intro i; cases i <;> simp⟩

inductive Reg where
 | size | width
 | idx : Index → Reg
 | rem : Index → Reg
 | addr | prod | tmp | cmp
 deriving DecidableEq, Fintype

abbrev CState (V : Type) := CounterLang.State Reg (Bool × V)

abbrev Prog (V : Type) := CounterLang.Program Reg (Bool × V)

lemma tableInput_length {N} (S : OrderedQuery.Data N) : (tableInput S).length = 8*(N*N) := by
 simp [tableInput]

lemma tableInput_lookup {N} (S : OrderedQuery.Data N) (r : Symbol) (a b : Fin N) :
 (tableInput S)[((OrderedQuery.symbolIndex r).val*N+a.val)*N+b.val]? =
   some (bitLetter (S.rel r a b)) := by
 have hi : ((OrderedQuery.symbolIndex r).val*N+a.val)*N+b.val =
     (OrderedQuery.cellIndex r a b).val := by
   simp [OrderedQuery.cellIndex,finProdFinEquiv]
   ring
 rw [hi]
 simp [tableInput,OrderedQuery.tableBits,OrderedQuery.cellValue_index]

def readCell {V} (k : ℕ) (i j : Index) (f : V → Option Letter → V) : Prog V :=
 .seq (.atom (.zero .addr))
 (.seq (repeatAdd .size .addr (by decide) k)
 (.seq (.atom (.add (.idx i) .addr (by simp)))
 (.seq (multiply .addr .size .prod .tmp (by decide) (by decide))
 (.seq (.atom (.add (.idx j) .prod (by simp)))
 (.seq (.atom (.lookup .prod (fun c a => (c.1,f c.2 a))))
 (.seq (.atom (.zero .addr)) (.atom (.zero .prod))))))))

lemma readCell_runs {V} (s : CState V) (k : ℕ) (i j : Index) (f : V → Option Letter → V)
   (haddr : s.nums .addr = 0) (hprod : s.nums .prod = 0) (htmp : s.nums .tmp = 0) :
 Runs (readCell k i j f) s
   {s with ctl := (false,f s.ctl.2 s.input[((k*s.nums .size+s.nums (.idx i))*s.nums .size+s.nums (.idx j))]?)}
   (16*k*(s.nums .size)^2+16*s.nums (.idx i)*s.nums .size +
     6*k*s.nums .size+8*k+16*s.nums .size+6*s.nums (.idx i)+16*s.nums (.idx j)+10*s.input.length+101) := by
 let s₁ := (Atom.zero .addr).eval s
 let s₂ : CState V := {s₁ with nums := Function.update s₁.nums .addr (s₁.nums .addr+k*s₁.nums .size)}
 let s₃ := (Atom.add (.idx i) .addr (by simp)).eval s₂
 let s₄ : CState V := {s₃ with ctl := (false,s₃.ctl.2), nums := Function.update (Function.update s₃.nums .prod (s₃.nums .addr*s₃.nums .size)) .tmp 0}
 let s₅ := (Atom.add (.idx j) .prod (by simp)).eval s₄
 let s₆ := (Atom.lookup .prod (fun c a => (c.1,f c.2 a))).eval s₅
 let s₇ := (Atom.zero .addr).eval s₆
 let s₈ := (Atom.zero .prod).eval s₇
 have hm := multiply_runs .addr .size .prod .tmp (by decide) (by decide) (by decide) (by decide) (by decide) s₃
 have h := (Runs.atom (.zero .addr) s).seq
   ((repeatAdd_runs .size .addr (by decide) k s₁).seq
   ((Runs.atom (.add (.idx i) .addr (by simp)) s₂).seq
   (hm.seq ((Runs.atom (.add (.idx j) .prod (by simp)) s₄).seq
   ((Runs.atom (.lookup .prod (fun c a => (c.1,f c.2 a))) s₅).seq
   ((Runs.atom (.zero .addr) s₆).seq (Runs.atom (.zero .prod) s₇)))))))
 have he : s₈ = {s with ctl := (false,f s.ctl.2 s.input[((k*s.nums .size+s.nums (.idx i))*s.nums .size+s.nums (.idx j))]?)} := by
   apply CounterLang.State.ext
   · simp [s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,Atom.eval,Function.update,Nat.add_comm]
   · funext r; cases r <;> simp [s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,Atom.eval,Function.update,haddr,hprod,htmp]
   · rfl
   · rfl
 change Runs (readCell k i j f) s s₈ _ at h
 rw [he] at h
 apply h.mono
 simp only [s₇,s₆,s₅,s₄,s₃,s₂,s₁,Atom.eval,Atom.cost]
 simp [Function.update,haddr,hprod,htmp]
 ; nlinarith

end CPTSeparation.TableMachine

namespace CPTSeparation.Bounded

section

open CounterLang TableMachine

inductive Program (V : Type) where
 | load (f : V → V)
 | emit (f : V → Letter)
 | cell (r : Symbol) (i j : Index) (f : V → Bool → V)
 | equal (i j : Index) (f : V → Bool → V)
 | seq (a b : Program V)
 | loop (i : Index) (body : Program V)

variable {V : Type}

def isOne (a : Option Letter) : Bool := a == some (some 1)

def Program.WF : Program V → Finset Index → Prop
 | .load _,_ => True
 | .emit _,_ => True
 | .cell _ _ _ _,_ => True
 | .equal _ _ _,_ => True
 | .seq a b,S => a.WF S ∧ b.WF S
 | .loop i b,S => i ∉ S ∧ b.WF (insert i S)

def Program.eval (N : ℕ) (table : List Letter) :
    Program V → (Index → ℕ) → V × List Letter → V × List Letter
 | .load f,_,s => (f s.1,s.2)
 | .emit f,_,s => (s.1,f s.1::s.2)
 | .cell r i j f,e,s => (f s.1 (isOne table[((OrderedQuery.symbolIndex r).val*N+e i)*N+e j]?),s.2)
 | .equal i j f,e,s => (f s.1 (e i == e j),s.2)
 | .seq a b,e,s => b.eval N table e (a.eval N table e s)
 | .loop i b,e,s => (List.range N).foldl (fun s k => b.eval N table (Function.update e i k) s) s

def equalCode (i j : Index) (f : V → Bool → V) : Prog V :=
 .seq (CounterLang.compare (.idx i) (.idx j) .addr .prod (by simp) (by simp) f)
   (.seq (.atom (.zero .addr)) (.atom (.zero .prod)))

def Program.compile : Program V → Prog V
 | .load f => .atom (.load (fun c => (false,f c.2)))
 | .emit f => .seq (.atom (.emit (fun c => f c.2))) (.atom (.load (fun c => (false,c.2))))
 | .cell r i j f => readCell (OrderedQuery.symbolIndex r).val i j (fun v a => f v (isOne a))
 | .equal i j f => equalCode i j f
 | .seq a b => .seq a.compile b.compile
 | .loop i b => .seq (.atom (.load (fun c => (false,c.2))))
   (forRange .size (.idx i) (.rem i) (by simp) b.compile)

def Program.time (N L : ℕ) : Program V → ℕ
 | .load _ => 1
 | .emit _ => 3
 | .cell _ _ _ _ => 1000*(N+1)^2+10*L
 | .equal _ _ _ => 100*(N+1)
 | .seq a b => 1+(a.time N L+b.time N L)
 | .loop _ b => (b.time N L+13)*N+22

def env (s : CState V) : Index → ℕ := fun i => s.nums (.idx i)

def result (s : CState V) (v : V × List Letter) : CState V :=
 {s with ctl := (false,v.1), output := v.2}

def Ready (S : Finset Index) (N : ℕ) (s : CState V) : Prop :=
 s.nums .size = N ∧ s.nums .addr = 0 ∧ s.nums .prod = 0 ∧ s.nums .tmp = 0 ∧
 (∀ i, s.nums (.idx i) ≤ N) ∧ (∀ i ∉ S, s.nums (.idx i) = 0 ∧ s.nums (.rem i) = 0)

@[simp] lemma ready_result {S N} (s : CState V) (v) : Ready S N (result s v) ↔ Ready S N s := Iff.rfl

@[simp] lemma env_result (s : CState V) (v) : env (result s v) = env s := rfl

@[simp] lemma result_result (s : CState V) (v w) : result (result s v) w = result s w := rfl

lemma ready_index {S N} (s : CState V) (hs : Ready S N s) (i : Index) (k : ℕ) (hk : k≤N) :
 Ready (insert i S) N (indexState (.idx i) (.rem i) N k s) := by
 rcases hs with ⟨hN,ha,hp,ht,hidx,hr⟩
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · simpa [indexState,Function.update] using hN
 · simpa [indexState,Function.update] using ha
 · simpa [indexState,Function.update] using hp
 · simpa [indexState,Function.update] using ht
 · intro j
   by_cases hji : j=i
   · subst j; simpa [indexState,Function.update] using hk
   · simpa [indexState,Function.update,hji] using hidx j
 · intro j hj
   have hh : j≠i ∧ j∉S := by simpa using hj
   simpa [indexState,Function.update,hh.1] using hr j hh.2

@[simp] lemma env_index (s : CState V) (i : Index) (N k) :
 env (indexState (.idx i) (.rem i) N k s) = Function.update (env s) i k := by
 funext j; by_cases h : j=i <;> simp [env,indexState,Function.update,h]

lemma equalCode_runs (i j : Index) (f : V → Bool → V) (s : CState V)
    (ha : s.nums .addr=0) (hp : s.nums .prod=0) (N : ℕ)
    (hi : s.nums (.idx i)≤N) (hj : s.nums (.idx j)≤N) :
 Runs (equalCode i j f) s (result s (f s.ctl.2 (s.nums (.idx i)==s.nums (.idx j)),s.output)) (100*(N+1)) := by
 let s₁ : CState V := {s with ctl := (false,f s.ctl.2 (decide (s.nums (.idx i)=s.nums (.idx j)))), nums := Function.update (Function.update s.nums .addr (s.nums (.idx i)-s.nums (.idx j))) .prod (s.nums (.idx j)-s.nums (.idx i))}
 let s₂ := (Atom.zero .addr).eval s₁
 have hc := compare_runs (.idx i) (.idx j) .addr .prod (by simp) (by simp) (by simp) (by decide) f s
 change Runs _ s s₁ _ at hc
 have h := hc.seq ((Runs.atom (.zero .addr) s₁).seq (Runs.atom (.zero .prod) s₂))
 have he : (Atom.zero .prod).eval s₂ = result s (f s.ctl.2 (s.nums (.idx i)==s.nums (.idx j)),s.output) := by
   apply CounterLang.State.ext
   · rfl
   · funext r; cases r <;> simp [s₂,s₁,Atom.eval,result,Function.update,ha,hp]
   · rfl
   · rfl
 rw [he] at h
 apply h.mono
 simp [s₂,s₁,Atom.cost,Atom.eval,Function.update,ha,hp]
 omega

lemma cell_runs (r : Symbol) (i j : Index) (f : V → Bool → V)
    (s : CState V) {S N} (hs : Ready S N s) :
 Runs (Program.compile (.cell r i j f)) s
   (result s ((Program.cell r i j f).eval N s.input (env s) (s.ctl.2,s.output)))
   (1000*(N+1)^2+10*s.input.length) := by
 have h := readCell_runs s (OrderedQuery.symbolIndex r).val i j (fun v a => f v (isOne a)) hs.2.1 hs.2.2.1 hs.2.2.2.1
 have he : s.nums .size=N := hs.1
 simp only [he] at h
 apply h.mono
 have hk : (OrderedQuery.symbolIndex r).val ≤ 8 := (OrderedQuery.symbolIndex r).isLt.le
 have hi := hs.2.2.2.2.1 i
 have hj := hs.2.2.2.2.1 j
 calc
  _ ≤ 16*8*N^2+16*N*N+6*8*N+8*8+16*N+6*N+16*N+10*s.input.length+101 := by gcongr
  _ ≤ _ := by nlinarith

lemma compile_runs (p : Program V) (S : Finset Index) (hw : p.WF S)
    (N : ℕ) (s : CState V) (hs : Ready S N s) :
 Runs p.compile s (result s (p.eval N s.input (env s) (s.ctl.2,s.output)))
   (p.time N s.input.length) := by
 induction p generalizing S s with
 | load f => exact Runs.atom (.load (fun c => (false,f c.2))) s
 | emit f =>
   exact (Runs.atom (.emit (fun c => f c.2)) s).seq
     (Runs.atom (.load (fun c => (false,c.2))) ((Atom.emit (fun c => f c.2)).eval s))
 | cell r i j f => exact cell_runs r i j f s hs
 | equal i j f => exact equalCode_runs i j f s hs.2.1 hs.2.2.1 N (hs.2.2.2.2.1 i) (hs.2.2.2.2.1 j)
 | seq a b iha ihb =>
   have ha := iha S hw.1 s hs
   have hb := ihb S hw.2 (result s (a.eval N s.input (env s) (s.ctl.2,s.output))) hs
   exact ha.seq hb
 | loop i b ih =>
   let e := env s
   let step := fun v k => b.eval N s.input (Function.update e i k) v
   let pref := fun k => (List.range k).foldl step (s.ctl.2,s.output)
   let st := fun k => result s (pref k)
   have hstep (k : ℕ) : pref (k+1) = step (pref k) k := by simp [pref,List.range_succ,step]
   have hbody (k : ℕ) (hk : k<N) :
       Runs b.compile (indexState (.idx i) (.rem i) N k (st k))
         (flag (indexState (.idx i) (.rem i) N k (st (k+1))) false) (b.time N s.input.length) := by
     have hr : Ready (insert i S) N (indexState (.idx i) (.rem i) N k (st k)) :=
       ready_index (st k) hs i k hk.le
     have h := ih (insert i S) hw.2 (indexState (.idx i) (.rem i) N k (st k)) hr
     rw [env_index] at h
     change Runs _ _ (result (indexState (.idx i) (.rem i) N k (st k)) (step (pref k) k)) _ at h
     rw [← hstep k] at h
     exact h
   have hi := hs.2.2.2.2.2 i hw.1
   have h := forRange_runs TableMachine.Reg.size (.idx i) (.rem i) (by simp) (by simp)
     b.compile st N (b.time N s.input.length)
     (by simpa [st,result] using hs.1)
     (by simpa [st,result] using hi.1) (by simpa [st,result] using hi.2)
     (by simpa [st,result] using hi.1) (by simpa [st,result] using hi.2)
     rfl hbody
   have hin : Runs (.atom (.load (fun c : Bool × V => (false,c.2)))) s (st 0) 1 := by
     simpa [st,pref,result,Atom.eval,Atom.cost] using Runs.atom (.load (fun c : Bool × V => (false,c.2))) s
   have total := hin.seq h
   convert total using 1 <;> first | rfl | (simp only [Program.time]; omega)

end

open CounterLang TableMachine

variable {V : Type}

abbrev Relation := Symbol → ℕ → ℕ → Bool

def readTable (N : ℕ) (w : List Letter) : Relation := fun r a b =>
 isOne w[((OrderedQuery.symbolIndex r).val*N+a)*N+b]?

def Program.interpret (N : ℕ) (rel : Relation) :
    Program V → (Index → ℕ) → V × List Letter → V × List Letter
 | .load f,_,s => (f s.1,s.2)
 | .emit f,_,s => (s.1,f s.1::s.2)
 | .cell r i j f,e,s => (f s.1 (rel r (e i) (e j)),s.2)
 | .equal i j f,e,s => (f s.1 (e i == e j),s.2)
 | .seq a b,e,s => b.interpret N rel e (a.interpret N rel e s)
 | .loop i b,e,s => (List.range N).foldl (fun s k => b.interpret N rel (Function.update e i k) s) s

lemma Program.eval_interpret (p : Program V) (N : ℕ) (w : List Letter) (e) (s) :
 p.eval N w e s = p.interpret N (readTable N w) e s := by
 induction p generalizing e s with
 | load _ => rfl
 | emit _ => rfl
 | cell _ _ _ _ => rfl
 | equal _ _ _ => rfl
 | seq a b iha ihb => simp only [Program.eval,Program.interpret,iha,ihb]
 | loop i b ih =>
   simp only [Program.eval,Program.interpret]
   congr 1
   funext s k
   exact ih _ _

lemma readTable_input {N} (S : OrderedQuery.Data N) (r : Symbol) (a b : Fin N) :
 readTable N (tableInput S) r a b = S.rel r a b := by
 rw [readTable,tableInput_lookup]
 cases h : S.rel r a b <;> decide +revert

lemma fold_emits {α : Type} (ls : List α) (step : V × List Letter → α → V × List Letter)
    (v : V) (chunk : α → List Letter)
    (h : ∀ a ∈ ls, ∀ out, step (v,out) a = (v,(chunk a).reverse++out)) (out) :
 ls.foldl step (v,out) = (v,(ls.flatMap chunk).reverse++out) := by
 induction ls generalizing out with
 | nil => rfl
 | cons a ls ih =>
   rw [List.foldl_cons,h a (by simp),ih (by intro b hb; exact h b (by simp [hb]))]
   simp [List.reverse_append,List.append_assoc]

lemma loop_emits (N : ℕ) (rel : Relation) (body : Program V) (i : Index)
    (e : Index → ℕ) (v : V) (chunk : ℕ → List Letter)
    (h : ∀ k<N, ∀ out, body.interpret N rel (Function.update e i k) (v,out) = (v,(chunk k).reverse++out))
    (out) :
 (Program.loop i body).interpret N rel e (v,out) =
   (v,((List.range N).flatMap chunk).reverse++out) := by
 exact fold_emits _ _ v chunk (by intro k hk; exact h k (List.mem_range.mp hk)) out

lemma Program.time_polynomial (p : Program V) :
 ∃ q : Polynomial ℕ, ∀ N, p.time N (8*(N*N)) = q.eval N := by
 induction p with
 | load f => exact ⟨1,by simp [Program.time]⟩
 | emit f => exact ⟨3,by simp [Program.time]⟩
 | cell r i j f => exact ⟨1000*(Polynomial.X+1)^2+80*Polynomial.X^2,by intro N; simp [Program.time]; ring⟩
 | equal i j f => exact ⟨100*(Polynomial.X+1),by simp [Program.time]⟩
 | seq a b iha ihb =>
   obtain ⟨p,hp⟩ := iha
   obtain ⟨q,hq⟩ := ihb
   exact ⟨1+(p+q),by intro N; simp [Program.time,hp,hq]⟩
 | loop i b ih =>
   obtain ⟨p,hp⟩ := ih
   exact ⟨(p+13)*Polynomial.X+22,by intro N; simp [Program.time,hp]⟩

end CPTSeparation.Bounded

end OAI
