import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.StackCompression

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteCode
noncomputable section
open StackMachine Structured.Program UniversalStack
variable {K Q R : Type*} [DecidableEq K]
def rename (e : Q ≃ R) (P : Q → StackMachine.Instr K Bool Q) : R → StackMachine.Instr K Bool R :=
  fun q => mapInstr e (P (e.symm q))
def config (e : Q ≃ R) (C : StackMachine.Config K Bool Q) : StackMachine.Config K Bool R := ⟨e C.state,C.store⟩
lemma rename_next (e : Q ≃ R) (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q) :
    next (rename e P) (config e C)=config e (next P C) := by
  cases h : P C.state <;> simp [next,rename,config,mapInstr,h]
lemma rename_exec (e : Q ≃ R) (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q) (n : ℕ) :
    exec (rename e P) (config e C) n=config e (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [exec,ih,rename_next];rfl
lemma exec_halt (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q)
    (h : P C.state=.halt) (n : ℕ) : exec P C n=C := by
  induction n with
  | zero => rfl
  | succ n ih => simp [exec,ih,next,h]
lemma after_halt (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q)
    {k n : ℕ} (hkn : k ≤ n) (h : P (exec P C k).state=.halt) : exec P C n=exec P C k := by
  rw [←Nat.add_sub_of_le hkn,exec_from,exec_halt P _ h]
lemma first_halt (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q)
    (n : ℕ) (h : P (exec P C n).state=.halt) :
    ∃ k, k ≤ n ∧ (∀t,t<k → P (exec P C t).state≠.halt) ∧
      P (exec P C k).state=.halt ∧ exec P C k=exec P C n := by
  classical
  have hh : ∃ k,P (exec P C k).state=.halt := ⟨n,h⟩
  let k := Nat.find hh
  have hk : k ≤ n := Nat.find_min' hh h
  have hs : P (exec P C k).state=.halt := Nat.find_spec hh
  exact ⟨k,hk,(fun t ht => Nat.find_min hh ht),hs,(after_halt P C hk hs).symm⟩
def enumeration [Fintype Q] (q : Q) : Q ≃ Fin (Fintype.card Q) :=
  (Fintype.equivFin Q).trans (Equiv.swap ((Fintype.equivFin Q) q) ⟨0,Fintype.card_pos_iff.mpr ⟨q⟩⟩)
lemma enumeration_zero [Fintype Q] (q : Q) : (enumeration q q).val=0 := by simp [enumeration]
def program [Fintype Q] (P : Q → StackMachine.Instr K Bool Q) (q : Q) (result : Q → Bool) :
    List (Instruction K) := programOf (rename (enumeration q) P) (result ∘ (enumeration q).symm)
lemma first_program_trace {m : ℕ} (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (C : StackMachine.Config K Bool (Fin m)) (n : ℕ) (b : Bool)
    (h : P (exec P C n).state=.halt) (hb : result (exec P C n).state=b) :
    ∃ t s front back,t ≤ (n+1)*(5*(encodeProgram (programOf P result)).length+3) ∧
      exec interpreter (UniversalStack.config .pick C.store (encodeProgram (programOf P result)) [] C.state.val) t=
        UniversalStack.config (.stopped b) s front back 0 := by
  obtain ⟨k,hkn,hpre,hs,he⟩ := first_halt P C n h
  have hr := finite_control_run P result C k hpre
  let q := (exec P C k).state
  have hq : P q=.halt := hs
  have hspl := programOf_split P result q
  simp only [instructionOf,hq] at hspl
  have hR : UniversalStack.Run (programOf P result) k C.state.val C.store
      ((programOf P result).take q.val).length (exec P C k).store := by
    simpa only [programOf_prefix_length] using hr
  obtain ⟨t,ht,H⟩ := simulate_halt (programOf P result)
    ((programOf P result).take q.val) ((programOf P result).drop (q.val+1)) (result q) hspl hR
  have hqb : result q=b := by simpa only [q,he] using hb
  rw [hqb] at H
  exact ⟨t,_,_,_,ht.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hkn 1)),H⟩
lemma program_trace [Fintype Q] (P : Q → StackMachine.Instr K Bool Q) (q : Q) (result : Q → Bool)
    (r : K → List Bool) (n : ℕ) (b : Bool) (h : P (exec P ⟨q,r⟩ n).state=.halt)
    (hb : result (exec P ⟨q,r⟩ n).state=b) :
    ∃ t s front back,t ≤ (n+1)*(5*(encodeProgram (program P q result)).length+3) ∧
      exec interpreter (UniversalStack.config .pick r (encodeProgram (program P q result)) [] 0) t=
        UniversalStack.config (.stopped b) s front back 0 := by
  let e := enumeration q
  have hE := rename_exec e P ⟨q,r⟩ n
  have hs : rename e P (exec (rename e P) (config e ⟨q,r⟩) n).state=.halt := by
    rw [hE];simp [rename,config,h,mapInstr]
  have hR : (result ∘ e.symm) (exec (rename e P) (config e ⟨q,r⟩) n).state=b := by
    rw [hE];simpa [config] using hb
  have H := first_program_trace (rename e P) (result ∘ e.symm) (config e ⟨q,r⟩) n b hs hR
  simpa only [program,config,e,enumeration_zero] using H
end
end SourceBurnside.FiniteCode

namespace SourceBurnside.LiteralCompiler
noncomputable section
open StackMachine Structured Structured.Program FixedArity
abbrev K := Option (Fin 2)
def src : K := some 1
def dst : K := some 0
lemma distinct : src≠dst := by decide
variable {A : Type*} [DecidableEq A] {m : ℕ}
def start (e : Option A ≃ Fin m) (P : Program A) (j : A) : CompactProgram.State e P j :=
  .inl (CompactProgram.boot e j).start
def result (e : Option A ≃ Fin m) (P : Program A) (j : A) : CompactProgram.State e P j → Bool
  | .inr (.start (.inr b)) => b
  | _ => false
def tokens (e : Option A ≃ Fin m) (P : Program A) (j out : A) :=
  UniversalStack.encodeProgram (FiniteCode.program (CompactProgram.machine e P j out) (start e P j) (result e P j))
def code (e : Option A ≃ Fin m) (P : Program A) (j out : A) : List Bool := WrappedInput.plain (tokens e P j out)
def loaderTime (ts : List (UniversalStack.Token K)) :=
  ((4*InitialFormula.binSize (WrappedInput.plain ts).length+3)+((UniversalInput.width K+1)*ts.length+
    UniversalInput.width K)+(2*ts.length+1))
def runTime (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) (n : ℕ) :=
  CompactProgram.bootTime e j x+CompactStacks.clock (CompactProgram.virtual e P out) (CompactProgram.initial e P j x) (n+1)
lemma input_regs (x : List Bool) :
    extendStore (CompactInit.store x [])=UniversalInput.inputRegs src dst [] x := by
  funext k
  cases k with
  | none => simp [extendStore,UniversalInput.inputRegs,src,dst]
  | some k => fin_cases k <;> simp [extendStore,CompactInit.store,UniversalInput.inputRegs,src,dst]
lemma compiled_trace (e : Option A ≃ Fin m) {P : Program A} (j out : A) (x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (CompactProgram.inputStore j x) n s) :
    ∃ t r front back, t ≤ (runTime e P j out x n+1)*(5*(tokens e P j out).length+3) ∧
      exec UniversalStack.interpreter
        (UniversalStack.config .pick (UniversalInput.inputRegs src dst [] x) (tokens e P j out) [] 0) t=
        UniversalStack.config (.stopped ((s out).getLast?.getD false)) r front back 0 := by
  have H := CompactProgram.answer_execution e j out x h
  let M := CompactProgram.machine e P j out
  let C := CompactProgram.initialConfig e P j x
  have hh : M (exec M C (runTime e P j out x n)).state=.halt := by
    change CompactProgram.machine e P j out _=.halt
    rw [show (exec M C (runTime e P j out x n)).state=_ from H]
    rfl
  have hb : result e P j (exec M C (runTime e P j out x n)).state=(s out).getLast?.getD false := by
    rw [show (exec M C (runTime e P j out x n)).state=_ from H]
    rfl
  have HC := FiniteCode.program_trace M (start e P j) (result e P j)
    (extendStore (CompactInit.store x [])) (runTime e P j out x n) ((s out).getLast?.getD false) hh hb
  simpa only [tokens,input_regs] using HC
lemma header_trace (e : Option A ≃ Fin m) {P : Program A} (j out : A) (x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (CompactProgram.inputStore j x) n s) :
    ∃ t r front back, t ≤ loaderTime (tokens e P j out)+(runTime e P j out x n+1)*(5*(tokens e P j out).length+3) ∧
      exec (WrappedInput.machine src dst)
        (WrappedInput.config src dst .header [] (WrappedInput.envelope (code e P j out) x) [] [] 0) t=
        WrappedInput.liftConfig (UniversalInput.liftConfig
          (UniversalStack.config (.stopped ((s out).getLast?.getD false)) r front back 0)) := by
  obtain ⟨t,r,front,back,ht,H⟩ := compiled_trace e j out x h
  have HL := WrappedInput.plain_trace src dst distinct (tokens e P j out) x
  refine ⟨loaderTime (tokens e P j out)+t,r,front,back,Nat.add_le_add_left ht _,?_⟩
  rw [UniversalStack.exec_from]
  change exec (WrappedInput.machine src dst) (exec (WrappedInput.machine src dst)
    (WrappedInput.config src dst .header [] (WrappedInput.envelope (WrappedInput.plain (tokens e P j out)) x) [] [] 0)
      (loaderTime (tokens e P j out))) t=_
  dsimp only [loaderTime]
  rw [HL]
  change exec (WrappedInput.machine src dst) (WrappedInput.liftConfig (UniversalInput.liftConfig
    (UniversalStack.config .pick (UniversalInput.inputRegs src dst [] x) (tokens e P j out) [] 0))) t=_
  rw [WrappedInput.lift_exec,UniversalInput.lift_exec src dst,H]
lemma specialized_trace (e : Option A ≃ Fin m) {P : Program A} (j out : A) (v x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (CompactProgram.inputStore j (InitialFormula.enc v.length++v++x)) n s) :
    ∃ t r front back,
      t ≤ (2*(WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length+1)+
        (4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+3)+
        (loaderTime (tokens e P j out)+(runTime e P j out (InitialFormula.enc v.length++v++x) n+1)*
          (5*(tokens e P j out).length+3)) ∧
      exec (WrappedInput.machine src dst)
        (WrappedInput.config src dst .reverse (WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x) [] [] [] 0) t=
        WrappedInput.liftConfig (UniversalInput.liftConfig
          (UniversalStack.config (.stopped ((s out).getLast?.getD false)) r front back 0)) := by
  obtain ⟨t,r,front,back,ht,H⟩ := header_trace e j out (InitialFormula.enc v.length++v++x) h
  let s0 := (2*(WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length+1)+
    (4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+3)
  refine ⟨s0+t,r,front,back,Nat.add_le_add_left ht s0,?_⟩
  rw [UniversalStack.exec_from,WrappedInput.raw_specialize_trace src dst distinct]
  exact H
end
end SourceBurnside.LiteralCompiler

namespace SourceBurnside.PolynomialAccounting
open Structured Structured.Binary
lemma powers (S : ℕ) (hS : 1 ≤ S) : 1 ≤ S^2 ∧ S ≤ S^2 ∧ 1 ≤ S^4 ∧ S^2 ≤ S^4 ∧ S ≤ S^4 := by
  have h2 : S ≤ S^2 := by nlinarith
  have h4 : S^2 ≤ S^4 := by nlinarith [sq_nonneg (S^2-S)]
  omega
def compactCoefficient (m c d : ℕ) := 3*m+7*d+4+(c+1)*(4*m*(2*(d+c+1)+1)+3)
lemma compact_bound (m c d L n S : ℕ) (hS : 1 ≤ S) (hL : L ≤ d*S) (hn : n ≤ c*S^2) :
    3*m+7*L+4+(n+1)*(4*m*(2*(L+(n+1))+1)+3) ≤ compactCoefficient m c d*S^4 := by
  obtain ⟨hs2,hsq,hs4,hs24,hs14⟩ := powers S hS
  have hl2 : L ≤ d*S^2 := hL.trans (Nat.mul_le_mul_left d hsq)
  have hl4 : L ≤ d*S^4 := hL.trans (Nat.mul_le_mul_left d hs14)
  have hboot : 3*m+7*L+4 ≤ (3*m+7*d+4)*S^4 := by
    have H := Nat.mul_le_mul_left (3*m+4) hs4
    nlinarith
  have hn1 : n+1 ≤ (c+1)*S^2 := by nlinarith
  have hln : L+(n+1) ≤ (d+c+1)*S^2 := by nlinarith
  have hi0 : 2*(L+(n+1))+1 ≤ (2*(d+c+1)+1)*S^2 := by nlinarith
  have hi1 := Nat.mul_le_mul_left (4*m) hi0
  have hi : 4*m*(2*(L+(n+1))+1)+3 ≤ (4*m*(2*(d+c+1)+1)+3)*S^2 := by nlinarith
  have hm := Nat.mul_le_mul hn1 hi
  unfold compactCoefficient
  nlinarith
lemma interpreter_bound (a b c S : ℕ) (hS : 1 ≤ S) (ha : a ≤ b*S^4) :
    (a+1)*c ≤ (b+1)*c*S^4 := by
  have hs4 := (powers S hS).2.2.1
  have H : a+1 ≤ (b+1)*S^4 := by nlinarith
  have := Nat.mul_le_mul_right c H
  nlinarith
lemma oneTape_bound (L N C d S : ℕ) (hS : 1 ≤ S) (hL : L ≤ d*S) (hN : N ≤ C*S^4) :
    N*(2*(L+N)+3) ≤ C*(2*(d+C)+3)*S^8 := by
  have hs4 := (powers S hS).2.2.1
  have hs14 := (powers S hS).2.2.2.2
  have hl4 := hL.trans (Nat.mul_le_mul_left d hs14)
  have hsum : 2*(L+N)+3 ≤ (2*(d+C)+3)*S^4 := by nlinarith
  have H := Nat.mul_le_mul hN hsum
  nlinarith
end SourceBurnside.PolynomialAccounting

namespace SourceBurnside.RawTimeBound
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open PolynomialAccounting
def size (h l : ℕ) (data : List Bool) := h+l+data.length+1
def quoteCost (v : List Bool) := (7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32
def inputCoefficient (v : List Bool) := 2*InitialFormula.binSize v.length+1+v.length+7
def coefficient (W D c : ℕ) (v : List Bool) :=
  let a := WrappedInput.specialize v v
  quoteCost v+5*a.length+39+
    (200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2)*(a.length+3)^2
lemma positive (h l : ℕ) (data : List Bool) : 1 ≤ size h l data := by unfold size;omega
lemma request_length (h l : ℕ) (data : List Bool) (z : Bool) :
    (RawHeader.request h l z data).length ≤ 7*size h l data := by
  have hh := InitialFormula.binSize_le_self h
  have hl := InitialFormula.binSize_le_self l
  simp only [RawHeader.request,List.length_append,List.length_cons,InitialFormula.enc_length]
  unfold size;omega
lemma twoinput_length (h l : ℕ) (data v : List Bool) (z : Bool) :
    (InitialFormula.enc v.length++v++RawHeader.request h l z data).length ≤ inputCoefficient v*size h l data := by
  have hh := request_length h l data z
  have hs := positive h l data
  simp only [List.length_append,InitialFormula.enc_length]
  have H := Nat.mul_le_mul_left (2*InitialFormula.binSize v.length+1+v.length) hs
  unfold inputCoefficient
  nlinarith
lemma envelope_length (h l : ℕ) (data a : List Bool) (z : Bool) :
    (WrappedInput.envelope a (RawHeader.request h l z data)).length ≤ inputCoefficient a*size h l data :=
  twoinput_length h l data a z
lemma arithmetic_size (h l : ℕ) (data a : List Bool) :
    RawPolynomial.size h l a data+1 ≤ (a.length+3)*size h l data := by
  have hl := InitialFormula.binSize_le_self l
  have hs := positive h l data
  have H := Nat.mul_le_mul_left (a.length+2) hs
  unfold RawPolynomial.size size at *
  nlinarith
lemma trace_bound (W D c h l : ℕ) (z : Bool) (data v : List Bool) :
    (7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32+
      (5*(WrappedInput.specialize v v).length+2+(5*(RawHeader.request h l z data).length+2))+
      (RawCompiled.setupBound W D h l (WrappedInput.specialize v v) data+
        c*(RawNumberPrep.width W D h (WrappedInput.specialize v v) data (InitialFormula.bin l)+1)^2) ≤
      coefficient W D c v*(size h l data)^2 := by
  let a := WrappedInput.specialize v v
  let S := size h l data
  have hs : 1 ≤ S := positive h l data
  have hs2 : 1 ≤ S^2 := (powers S hs).1
  have hsq : S ≤ S^2 := (powers S hs).2.1
  have hreq : (RawHeader.request h l z data).length ≤ 7*S^2 :=
    (request_length h l data z).trans (Nat.mul_le_mul_left 7 hsq)
  have hsz := arithmetic_size h l data a
  have hsz2 : (RawPolynomial.size h l a data+1)^2 ≤ (a.length+3)^2*S^2 := by
    calc _ ≤ ((a.length+3)*S)^2 := Nat.pow_le_pow_left hsz 2
         _ = _ := by ring
  have hsetup := RawPolynomial.setup_le W D h l a data
  have hbody := RawPolynomial.body_le W D h l c a data
  have hab : RawCompiled.setupBound W D h l a data+
      c*(RawNumberPrep.width W D h a data (InitialFormula.bin l)+1)^2 ≤
      (200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2)*
        (RawPolynomial.size h l a data+1)^2 := by nlinarith only [hsetup,hbody]
  have hscale := Nat.mul_le_mul_left (200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2) hsz2
  have hconst := Nat.mul_le_mul_left (quoteCost v+5*a.length+4) hs2
  change quoteCost v+(5*a.length+2+(5*(RawHeader.request h l z data).length+2))+_ ≤ _
  change _ ≤ (quoteCost v+5*a.length+39+(200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2)*(a.length+3)^2)*S^2
  nlinarith only [hab,hscale,hconst,hreq]
end SourceBurnside.RawTimeBound

namespace SourceBurnside.LiteralCompiler
noncomputable section
open PolynomialAccounting
variable {A : Type*} [DecidableEq A] {m : ℕ}
def coefficient (m c din draw : ℕ) (spec : List Bool) (ts : List (UniversalStack.Token K)) :=
  2*draw+4+4*InitialFormula.binSize spec.length+loaderTime ts+
    (compactCoefficient m c din+1)*(5*ts.length+3)
lemma specialized_bound (e : Option A ≃ Fin m) (P : Structured.Program A) (j out : A) (v x : List Bool)
    (n S c din draw : ℕ) (hS : 1 ≤ S)
    (hx : (InitialFormula.enc v.length++v++x).length ≤ din*S)
    (hr : (WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length ≤ draw*S)
    (hn : n ≤ c*S^2) :
    (2*(WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length+1)+
        (4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+3)+
        (loaderTime (tokens e P j out)+(runTime e P j out (InitialFormula.enc v.length++v++x) n+1)*
          (5*(tokens e P j out).length+3)) ≤
      coefficient m c din draw (WrappedInput.specialize (code e P j out) v) (tokens e P j out)*S^4 := by
  let xs := InitialFormula.enc v.length++v++x
  have hc := CompactProgram.time_bound e P j out xs (n+1)
  have HB := compact_bound m c din xs.length n S hS hx hn
  have hRun : runTime e P j out xs n ≤ compactCoefficient m c din*S^4 := hc.trans HB
  have hI := interpreter_bound (runTime e P j out xs n) (compactCoefficient m c din)
    (5*(tokens e P j out).length+3) S hS hRun
  have hs4 := (powers S hS).2.2.1
  have hs14 := (powers S hS).2.2.2.2
  have hRaw := hr.trans (Nat.mul_le_mul_left draw hs14)
  have hconst := Nat.mul_le_mul_left
    (4+4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+loaderTime (tokens e P j out)) hs4
  unfold coefficient
  change _ ≤ (2*draw+4+4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+
    loaderTime (tokens e P j out)+(compactCoefficient m c din+1)*(5*(tokens e P j out).length+3))*S^4
  nlinarith only [hI,hRaw,hconst]
end
end SourceBurnside.LiteralCompiler

namespace SourceBurnside.RawFixedPoint
noncomputable section
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    (RawFit.body β g D c output blank initial accept encoding).Exponents
      (RawPreparedInputs.bound D h code data l) (RawPreparedInputs.semantic code h l z data) := by
  apply exponents_mono _ (RawFit.body_exponents β g D c output blank initial accept encoding (RawPreparedInputs.semantic code h l z data))
  change RawLocalBody.limit D h code.length ≤ RawPreparedInputs.bound D h code data l
  unfold RawPreparedInputs.bound;omega
lemma body_boolean (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Fin 7 → ℕ) :
    (RawFit.body β g D c output blank initial accept encoding).eval v ≤ 1 := by
  have Hbody : (RawLocalBody.body β g D c output blank initial accept encoding).eval v ≤ 1 := by
    rw [RawLocalBody.body,bind_eval]
    unfold LocalBody.body
    simp only [PredicateFormula.normalEntry,PredicateFormula.rawUnaryZero,PredicateFormula.rawBinaryZero,
      PredicateFormula.rawUnaryRep,PredicateFormula.rawBinaryRep,PredicateFormula.unaryRep,PredicateFormula.binaryRep,
      CellFormula.unaryZero,CellFormula.binaryZero,PredicateFormula.branch_value,all_eval,any_eval]
    split_ifs <;> norm_num [eval]
  rw [RawFit.body_eval]
  split
  · simp only [RawLocalBody.checkedBody,and_eval];split <;> omega
  · split <;> omega

theorem construct (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) (hBool : ∀v,e.eval v ≤ 1) :
    ∃t : List Bool, ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool), ∃r front back,
        Add.bit b=e.eval (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        StackMachine.exec (WrappedInput.machine LiteralCompiler.src LiteralCompiler.dst)
          (WrappedInput.config LiteralCompiler.src LiteralCompiler.dst .reverse
            (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)) [] [] [] 0) N=
          WrappedInput.liftConfig (UniversalInput.liftConfig
            (UniversalStack.config (.stopped b) r front back 0)) := by
  obtain ⟨R,hR⟩ := TwoInputBody.trace e D hE
  let K := TwoInputBody.K R
  let : Fintype K := Fintype.ofFinite K
  let p := TwoInputBody.program R e.weight D
  let j := TwoInputBody.source R
  let out : K := .inr (.inr R.out)
  let f := Fintype.equivFin (Option K)
  let t := LiteralCompiler.code f p j out
  refine ⟨t,?_⟩
  intro h l z data
  obtain ⟨n,y,hn,hy,hyv,H⟩ := hR t h l z data
  have HH : Run p (CompactProgram.inputStore j (InitialFormula.enc t.length++t++RawHeader.request h l z data)) n
      (Sum.elim (TwoInputQuote.store (RawHeader.request h l z data) (InitialFormula.bin t.length) t 0
        (WrappedInput.specialize t t).reverse)
      (Function.update (RawCompiled.prepared R (RawNumberPrep.width e.weight D h (WrappedInput.specialize t t) data
        (InitialFormula.bin l)) (WrappedInput.specialize t t) h l z data) (.inr R.out) y)) := H
  obtain ⟨N,r,front,back,hN,HC⟩ := LiteralCompiler.specialized_trace f j out t (RawHeader.request h l z data) HH
  have hout : (Sum.elim (TwoInputQuote.store (RawHeader.request h l z data) (InitialFormula.bin t.length) t 0
        (WrappedInput.specialize t t).reverse)
      (Function.update (RawCompiled.prepared R (RawNumberPrep.width e.weight D h (WrappedInput.specialize t t) data
        (InitialFormula.bin l)) (WrappedInput.specialize t t) h l z data) (.inr R.out) y)) out=y := by
    simp [out]
  rw [hout] at HC
  refine ⟨N,y.getLast?.getD false,r,front,back,?_,HC⟩
  rw [FixedArity.output_bit,hyv,Nat.mod_eq_of_lt]
  have := hBool (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data)
  omega

theorem source_predicate_selfpoint (β g D : ℕ) (c : Tableau.Circuit (3*β) g)
    (output : Fin β → Tableau.Wire (3*β+g)) (blank initial accept : Fin β → Bool)
    (encoding : Bool → Fin β → Bool) :
    ∃t : List Bool, ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool), ∃r front back,
        Add.bit b=(RawFit.body β g D c output blank initial accept encoding).eval
          (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        StackMachine.exec (WrappedInput.machine LiteralCompiler.src LiteralCompiler.dst)
          (WrappedInput.config LiteralCompiler.src LiteralCompiler.dst .reverse
            (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)) [] [] [] 0) N=
          WrappedInput.liftConfig (UniversalInput.liftConfig
            (UniversalStack.config (.stopped b) r front back 0)) :=
  construct _ D (body_exponents β g D c output blank initial accept encoding)
    (body_boolean β g D c output blank initial accept encoding)
end
end SourceBurnside.RawFixedPoint

namespace SourceBurnside.RawFixedPoint
noncomputable section
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
theorem constructTimed (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) (hBool : ∀v,e.eval v ≤ 1) :
    ∃(t : List Bool) (C : ℕ), ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool), ∃r front back,
        N ≤ C*(RawTimeBound.size h l data)^4 ∧
        Add.bit b=e.eval (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        StackMachine.exec (WrappedInput.machine LiteralCompiler.src LiteralCompiler.dst)
          (WrappedInput.config LiteralCompiler.src LiteralCompiler.dst .reverse
            (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)) [] [] [] 0) N=
          WrappedInput.liftConfig (UniversalInput.liftConfig
            (UniversalStack.config (.stopped b) r front back 0)) := by
  obtain ⟨R,hR⟩ := TwoInputBody.trace e D hE
  let K := TwoInputBody.K R
  let : Fintype K := Fintype.ofFinite K
  let p := TwoInputBody.program R e.weight D
  let j := TwoInputBody.source R
  let out : K := .inr (.inr R.out)
  let f := Fintype.equivFin (Option K)
  let t := LiteralCompiler.code f p j out
  let C := LiteralCompiler.coefficient (Fintype.card (Option K))
    (RawTimeBound.coefficient e.weight D R.coefficient t)
    (RawTimeBound.inputCoefficient t) (RawTimeBound.inputCoefficient (WrappedInput.specialize t t))
    (WrappedInput.specialize t t) (LiteralCompiler.tokens f p j out)
  refine ⟨t,C,?_⟩
  intro h l z data
  obtain ⟨n,y,hn,hy,hyv,H⟩ := hR t h l z data
  have HH : Run p (CompactProgram.inputStore j (InitialFormula.enc t.length++t++RawHeader.request h l z data)) n
      (Sum.elim (TwoInputQuote.store (RawHeader.request h l z data) (InitialFormula.bin t.length) t 0
        (WrappedInput.specialize t t).reverse)
      (Function.update (RawCompiled.prepared R (RawNumberPrep.width e.weight D h (WrappedInput.specialize t t) data
        (InitialFormula.bin l)) (WrappedInput.specialize t t) h l z data) (.inr R.out) y)) := H
  obtain ⟨N,r,front,back,hN,HC⟩ := LiteralCompiler.specialized_trace f j out t (RawHeader.request h l z data) HH
  have hout : (Sum.elim (TwoInputQuote.store (RawHeader.request h l z data) (InitialFormula.bin t.length) t 0
        (WrappedInput.specialize t t).reverse)
      (Function.update (RawCompiled.prepared R (RawNumberPrep.width e.weight D h (WrappedInput.specialize t t) data
        (InitialFormula.bin l)) (WrappedInput.specialize t t) h l z data) (.inr R.out) y)) out=y := by
    simp [out]
  rw [hout] at HC
  have hnn := hn.trans (RawTimeBound.trace_bound e.weight D R.coefficient h l z data t)
  have htime := LiteralCompiler.specialized_bound f p j out t (RawHeader.request h l z data)
    n (RawTimeBound.size h l data) (RawTimeBound.coefficient e.weight D R.coefficient t)
    (RawTimeBound.inputCoefficient t) (RawTimeBound.inputCoefficient (WrappedInput.specialize t t))
    (RawTimeBound.positive h l data) (RawTimeBound.twoinput_length h l data t z)
    (RawTimeBound.envelope_length h l data (WrappedInput.specialize t t) z) hnn
  refine ⟨N,y.getLast?.getD false,r,front,back,hN.trans htime,?_,HC⟩
  rw [FixedArity.output_bit,hyv,Nat.mod_eq_of_lt]
  have := hBool (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data)
  omega
end
end SourceBurnside.RawFixedPoint

namespace SourceBurnside.TimedTape
noncomputable section
open StackMachine Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
abbrev K := LiteralCompiler.K
abbrev SK := UniversalStack.Stack K
abbrev TK := UniversalStack.Token K
abbrev SQ := WrappedInput.State K
abbrev Γ := StackMachine.Symbol SK TK
abbrev Q := StackMachine.State SK TK SQ
def machine := WrappedInput.machine LiteralCompiler.src LiteralCompiler.dst
def δ := StackMachine.compile machine
def start (x : List Bool) : StackMachine.Config SK TK SQ :=
  WrappedInput.config LiteralCompiler.src LiteralCompiler.dst .reverse x [] [] [] 0
def finish (b : Bool) (r : K → List Bool) (front back : List TK) : StackMachine.Config SK TK SQ :=
  WrappedInput.liftConfig (UniversalInput.liftConfig (UniversalStack.config (.stopped b) r front back 0))
def blank : Γ := ⟨false,fun _ => none⟩
def origin : Γ := ⟨true,fun _ => none⟩
def bitSymbol (b : Bool) : Γ := ⟨false,fun k => if k=.reg LiteralCompiler.src then some (.bit b) else none⟩
def initialState : Q := .ready .reverse
def finalState (b : Bool) : Q := .ready (.inner (.universal (.stopped b)))
def output (b : Bool) : OneTape.Label Γ Q := ⟨origin,true,some (finalState b)⟩
lemma start_length (x : List Bool) (k : SK) : ((start x).store k).length ≤ x.length := by
  cases k with
  | reg k =>
    simp only [start,WrappedInput.config,UniversalStack.config,UniversalInput.inputRegs]
    split_ifs <;> simp
  | front => simp [start,WrappedInput.config,UniversalStack.config]
  | back => simp [start,WrappedInput.config,UniversalStack.config]
  | pc => simp [start,WrappedInput.config,UniversalStack.config]
lemma finish_halt (b : Bool) (r : K → List Bool) (front back : List TK) :
    machine (finish b r front back).state=.halt := rfl
lemma origin_tape (r : SK → List TK) : StackMachine.tape r 0=origin := by
  rfl
lemma finish_output (b : Bool) (r : K → List Bool) (front back : List TK) :
    (StackMachine.encode (finish b r front back)).cell 0=output b := by
  simp [StackMachine.encode,StackMachine.place,OneTape.Config.cell,finish,output,
    finalState,WrappedInput.liftConfig,UniversalInput.liftConfig,UniversalStack.config,origin_tape]
lemma frozen (b : Bool) : ∀ s,δ (finalState b) s=⟨s,finalState b,.stay⟩ := by intro s;rfl
lemma output_injective : Function.Injective output := by
  intro b c h
  have H := congrArg OneTape.Label.head h
  simpa [output,finalState] using H
lemma construct (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) (hBool : ∀v,e.eval v ≤ 1) :
    ∃(t : List Bool) (C : ℕ), ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool),
        N ≤ C*(RawTimeBound.size h l data)^8 ∧
        Add.bit b=e.eval (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        ∀T≥N,(OneTape.run δ (StackMachine.encode
          (start (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)))) T).cell 0=output b := by
  obtain ⟨t,C,hC⟩ := RawFixedPoint.constructTimed e D hE hBool
  refine ⟨t,C*(2*(RawTimeBound.inputCoefficient (WrappedInput.specialize t t)+C)+3),?_⟩
  intro h l z data
  obtain ⟨N,b,r,front,back,hN,hb,HC⟩ := hC h l z data
  let X := WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)
  change StackMachine.exec machine (start X) N=finish b r front back at HC
  refine ⟨StackMachine.clock machine (start X) N,b,?_,hb,?_⟩
  · have H := StackMachine.clock_bound machine (start X) X.length N (start_length X)
    exact H.trans (PolynomialAccounting.oneTape_bound X.length N C
      (RawTimeBound.inputCoefficient (WrappedInput.specialize t t)) (RawTimeBound.size h l data)
      (RawTimeBound.positive h l data) (RawTimeBound.envelope_length h l data (WrappedInput.specialize t t) z) hN)
  · intro T hT
    have ht := StackMachine.compile_finish machine (start X) N T
      (by rw [HC];exact finish_halt b r front back) hT
    rw [HC] at ht
    change (OneTape.run (StackMachine.compile machine) (StackMachine.encode (start X)) T).cell 0=output b
    rw [ht,finish_output]
lemma source_predicate (β g D : ℕ) (c : Tableau.Circuit (3*β) g)
    (out : Fin β → Tableau.Wire (3*β+g)) (bl ini acc : Fin β → Bool)
    (encoding : Bool → Fin β → Bool) :
    ∃(t : List Bool) (C : ℕ), ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool),
        N ≤ C*(RawTimeBound.size h l data)^8 ∧
        Add.bit b=(RawFit.body β g D c out bl ini acc encoding).eval
          (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        ∀T≥N,(OneTape.run δ (StackMachine.encode
          (start (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)))) T).cell 0=output b :=
  construct _ D (RawFixedPoint.body_exponents β g D c out bl ini acc encoding)
    (RawFixedPoint.body_boolean β g D c out bl ini acc encoding)
end
end SourceBurnside.TimedTape

namespace SourceBurnside.Tableau

inductive Formula (n : ℕ)
  | constant (b : Bool)
  | input (i : Fin n)
  | nand (a b : Formula n)

namespace Formula
variable {n m : ℕ}
def eval (v : Fin n → Bool) : Formula n → Bool
  | .constant b => b
  | .input i => v i
  | .nand a b => Tableau.nand (a.eval v) (b.eval v)
def map (f : Fin n → Fin m) : Formula n → Formula m
  | .constant b => .constant b
  | .input i => .input (f i)
  | .nand a b => .nand (a.map f) (b.map f)
@[simp] lemma eval_map (f : Fin n → Fin m) (a : Formula n) (v : Fin m → Bool) :
    (a.map f).eval v=a.eval (v ∘ f) := by induction a <;> simp_all [map,eval]
def neg (a : Formula n) : Formula n := .nand a a
def conj (a b : Formula n) : Formula n := neg (.nand a b)
def disj (a b : Formula n) : Formula n := .nand a.neg b.neg
def mux (b x y : Formula n) : Formula n := (b.conj x).disj (b.neg.conj y)
lemma eval_mux (b x y : Formula n) (v : Fin n → Bool) :
    (mux b x y).eval v = if b.eval v then x.eval v else y.eval v := by
  unfold mux conj disj neg
  simp only [eval]
  cases b.eval v <;> cases x.eval v <;> cases y.eval v <;> decide

theorem represents (f : (Fin n → Bool) → Bool) : ∃ a : Formula n, ∀ v, a.eval v=f v := by
  induction n with
  | zero =>
    refine ⟨.constant (f Fin.elim0),?_⟩
    intro v
    have hv : v=Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [eval,hv]
  | succ n ih =>
    obtain ⟨a,ha⟩ := ih (fun v => f (Fin.cons true v))
    obtain ⟨b,hb⟩ := ih (fun v => f (Fin.cons false v))
    refine ⟨mux (.input 0) (a.map Fin.succ) (b.map Fin.succ),?_⟩
    intro v
    rw [eval_mux,eval_map,eval_map,ha,hb]
    change (if v 0 then f (Fin.cons true (v ∘ Fin.succ)) else
      f (Fin.cons false (v ∘ Fin.succ)))=f v
    have he : Fin.cons (v 0) (v ∘ Fin.succ)=v := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    cases hh : v 0 <;> simpa only [hh,Bool.false_eq_true,ite_false,ite_true] using congrArg f he
end Formula

namespace Circuit
variable {I g h k : ℕ}

def rename (le : g≤h) (w : Wire (I+g)) : Wire (I+h) :=
  w.map id (Fin.castLE (Nat.add_le_add_left le I))

structure Extension (c : Circuit I g) (d : Circuit I h) : Prop where
  le : g≤h
  agree : ∀ v i, d.evaluate v (Fin.castLE (Nat.add_le_add_left le I) i)=c.evaluate v i

lemma Extension.refl (c : Circuit I g) : Extension c c := ⟨le_refl _,fun _ _ => rfl⟩
lemma Extension.trans {c : Circuit I g} {d : Circuit I h} {e : Circuit I k}
    (hc : Extension c d) (hd : Extension d e) : Extension c e := by
  refine ⟨hc.le.trans hd.le,?_⟩
  intro v i
  have he := hd.agree v (Fin.castLE (Nat.add_le_add_left hc.le I) i)
  exact he.trans (hc.agree v i)
lemma extension_snoc (c : Circuit I g) (a b : Wire (I+g)) : Extension c (c.snoc a b) := by
  refine ⟨Nat.le_succ g,?_⟩
  intro v i
  change Fin.lastCases (motive:=fun _ => Bool) _ (c.evaluate v) (Fin.castSucc i)=_
  exact Fin.lastCases_castSucc i
lemma Extension.wire {c : Circuit I g} {d : Circuit I h} (he : Extension c d)
    (w : Wire (I+g)) (v : Fin I → Bool) : (rename he.le w).eval (d.evaluate v)=w.eval (c.evaluate v) := by
  cases w with
  | inl b => rfl
  | inr i => exact he.agree v i

theorem compile_formula {n : ℕ} (a : Formula n) (c : Circuit I g)
    (env : Fin n → Wire (I+g)) : ∃ h, ∃ d : Circuit I h, ∃ _ : Extension c d,
      ∃ w : Wire (I+h), ∀ v, w.eval (d.evaluate v)=a.eval (fun i => (env i).eval (c.evaluate v)) := by
  induction a generalizing g with
  | constant b => exact ⟨g,c,Extension.refl c,.inl b,fun _ => rfl⟩
  | input i => exact ⟨g,c,Extension.refl c,env i,fun _ => rfl⟩
  | nand a b ia ib =>
    obtain ⟨g₁,c₁,e₁,w₁,hw₁⟩ := ia c env
    let env₁ := fun i => rename e₁.le (env i)
    obtain ⟨g₂,c₂,e₂,w₂,hw₂⟩ := ib c₁ env₁
    let w₁' := rename e₂.le w₁
    refine ⟨g₂+1,c₂.snoc w₁' w₂,(e₁.trans e₂).trans (extension_snoc _ _ _),
      .inr (Fin.last _),?_⟩
    intro v
    change Fin.lastCases (motive:=fun _ => Bool) _ _ (Fin.last _)=_
    rw [Fin.lastCases_last]
    rw [e₂.wire w₁ v,hw₁ v,hw₂ v]
    have hen : (fun i => (env₁ i).eval (c₁.evaluate v))=fun i => (env i).eval (c.evaluate v) := by
      funext i; exact e₁.wire (env i) v
    rw [hen]
    rfl

theorem compile_outputs {n m : ℕ} (a : Fin m → Formula n) (c : Circuit I g)
    (env : Fin n → Wire (I+g)) : ∃ h, ∃ d : Circuit I h, ∃ _ : Extension c d,
      ∃ w : Fin m → Wire (I+h), ∀ v r,
        (w r).eval (d.evaluate v)=(a r).eval (fun i => (env i).eval (c.evaluate v)) := by
  induction m with
  | zero => exact ⟨g,c,Extension.refl c,Fin.elim0,fun _ r => Fin.elim0 r⟩
  | succ m ih =>
    obtain ⟨g₁,c₁,e₁,w₁,hw₁⟩ := ih (fun r => a r.castSucc)
    let env₁ := fun i => rename e₁.le (env i)
    obtain ⟨g₂,c₂,e₂,w₂,hw₂⟩ := compile_formula (a (Fin.last m)) c₁ env₁
    refine ⟨g₂,c₂,e₁.trans e₂,Fin.lastCases w₂ (fun r => rename e₂.le (w₁ r)),?_⟩
    intro v r
    refine Fin.lastCases ?_ (fun j => ?_) r
    · simp only [Fin.lastCases_last]
      rw [hw₂]
      congr 1
      funext i
      exact e₁.wire (env i) v
    · simp only [Fin.lastCases_castSucc]
      rw [e₂.wire,hw₁]

end Circuit

theorem exists_nand_circuit {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) :
    ∃ g, ∃ c : Circuit n g, ∃ out : Fin m → Wire (n+g),
      ∀ v r, (out r).eval (c.evaluate v)=f v r := by
  classical
  choose a ha using fun r => Formula.represents (fun v => f v r)
  obtain ⟨g,c,_,out,ho⟩ := Circuit.compile_outputs a (Circuit.nil (inputs:=n)) (fun i => .inr i)
  refine ⟨g,c,out,?_⟩
  intro v r
  exact (ho v r).trans (ha r v)

end SourceBurnside.Tableau

end

end OAI
