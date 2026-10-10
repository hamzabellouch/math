import OAI.Computability.WeisfeilerLeman.RAMSimulation

namespace OAI

universe uK uX

namespace WLTime.TypedStack.Code
variable {K : Type uK} {X : Type uX} [DecidableEq K]
abbrev HaltState (c : Code K X) := c.State ⊕ Unit
def haltTransition (c : Code K X) (answer : Tops K X → Bool) :
    HaltState c → Tops K X → Command K X (HaltState c)
  | .inl q,v => Command.redirect Sum.inl (.inr ()) (c.transition q v)
  | .inr _,v => .halt (answer v)
def haltMachine (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool) :
    Machine K X (HaltState c) where
  inputStack := input
  inputLetter := letter
  initial := .inl c.entry
  transition := haltTransition c answer
 theorem haltMachine_run (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool)
    (w : List Bool) {t out} (h : c.Exec (fun r => if r=input then w.map letter else []) t out) :
    ((haltMachine c input letter answer).run w (t+1)).state=.inl (answer (tops out)) := by
  have he := (exec_finite h).plug Sum.inl (.inr ()) (fun _ _ => rfl)
    (Execution.halt (tr:=haltTransition c answer) (q:=.inr ()) (s:=out) rfl)
  exact congrArg Config.state (he.iterate (haltMachine c input letter answer))
variable [Fintype K] [Fintype X]
noncomputable def haltOneTape (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool) : OneTape :=
  (haltMachine c input letter answer).compile.oneTape
 theorem haltOneTape_correct (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool)
    (w : List Bool) {t out} (h : c.Exec (fun r => if r=input then w.map letter else []) t out) :
    (haltOneTape c input letter answer).toTM.halts w ∧
    (haltOneTape c input letter answer).toTM.time w≤8*(Fintype.card K+1)*(w.length+t+2)^2 ∧
    ((haltOneTape c input letter answer).toTM.accepts w ↔ answer (tops out)=true) := by
  have hr := haltMachine_run c input letter answer w h
  have he := (haltMachine c input letter answer).oneTape_correct w (t+1) (answer (tops out)) hr
  simpa only [haltOneTape,show w.length+(t+1)+1=w.length+t+2 by omega] using he
end WLTime.TypedStack.Code

namespace WLTime.RAMAlphabet
open scoped Classical
noncomputable section
variable (A : RAM)
def budgetConstant : ℕ := 100*(A.registers+1)+constant A*depth A*(depth A+1)+A.locations+2
 theorem budget_bound (w len time : ℕ) :
    budget A w len time≤budgetConstant A*(w+1)^exponent A*(len+time+1)^2 := by
  let W := (w+1)^exponent A
  let X := len+time+1
  have he : 1≤exponent A := by unfold exponent; omega
  have hw : w+1≤W := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<w+1) he
  have hW : 1≤W := by omega
  have hX : 1≤X := by dsimp [X]; omega
  have ht : time≤X := by dsimp [X]; omega
  have hl : len+1≤X := by dsimp [X]; omega
  have hXX : X≤X^2 := Nat.le_self_pow (by decide) X
  have hi : initBound A w len≤100*(A.registers+1)*W*X^2 := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ hw) hl).trans (Nat.mul_le_mul_left _ hXX)
  have hc := unitCost_bound A w
  have hL : len+time*depth A+depth A+1≤(depth A+1)*X := by dsimp [X]; nlinarith
  have hs : stepBound A w (len+time*depth A)≤constant A*W*depth A*((depth A+1)*X)+A.locations := by
    unfold stepBound
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) hL) _
  have hremain : (stepBound A w (len+time*depth A)+1)*time+1≤
      (constant A*depth A*(depth A+1)+A.locations+2)*W*X^2 := by
    have hz : stepBound A w (len+time*depth A)+1≤
        (constant A*depth A*(depth A+1)+A.locations+1)*W*X := by
      have hWX : 1≤W*X := Nat.mul_le_mul hW hX
      have hP := Nat.mul_le_mul_left (A.locations+1) hWX
      nlinarith only [hs,hP]
    have hmul := Nat.mul_le_mul hz ht
    have hWX2 : 1≤W*X^2 := Nat.mul_le_mul hW (one_le_pow₀ hX)
    nlinarith only [hmul,hWX2]
  dsimp only [budget,budgetConstant]
  change initBound A w len+(stepBound A w (len+time*depth A)+1)*time+1≤
    (100*(A.registers+1)+constant A*depth A*(depth A+1)+A.locations+2)*W*X^2
  nlinarith only [hi,hremain]
end
end WLTime.RAMAlphabet

namespace WLTime.TypedStack.Code
theorem Exec.of_decEq {K : Type uK} {X : Type uX} {i j : DecidableEq K} {c : Code K X} {s t out}
    (h : @Exec K X i c s t out) : @Exec K X j c s t out := by
  have he : i=j := Subsingleton.elim _ _
  cases he
  exact h
end WLTime.TypedStack.Code

namespace WLTime.RAMConsumer
open TypedStack
noncomputable section
variable {K : Type uK} [DecidableEq K] (A : RAM)
abbrev Reg (K : Type uK) := K ⊕ RAMAlphabet.Reg A
abbrev Letter := RAMAlphabet.Letter A
local instance : DecidableEq (RAMAlphabet.Reg A) := Classical.decEq _
local instance : DecidableEq (Letter A) := Classical.decEq _
def prelude (c : Code K Bool) (output : K) : Code (Reg A K) (Letter A) :=
  .seq ((c.mapLetters Sum.inl (RAMAlphabet.decode A)).relabel Sum.inl)
    (.transfer (.inl output) (.inr (.inl 0)) (.inl false))
def code (c : Code K Bool) (output : K) (w : ℕ) : Code (Reg A K) (Letter A) :=
  .seq (prelude A c output) ((RAMAlphabet.program A w).relabel Sum.inr)
def answer (v : Tops (Reg A K) (Letter A)) : Bool :=
  !((v (.inr (.inl 13))).map (RAMAlphabet.decode A)).getD false
 theorem prefix_exec (c : Code K Bool) (output : K) {s t out} (h : c.Exec s t out)
    (ys : List Bool) (ho : out output=ys.reverse) :
    (prelude A c output).Exec (Sum.elim (Code.listMap Sum.inl s) (fun _ => []))
      (t+(5*ys.length+1))
      (Sum.elim (Function.update (Code.listMap Sum.inl out) output []) (RAMAlphabet.inputState A ys)) := by
  have hc := Code.relabel_inl_exec
    (Code.mapLetters_exec Sum.inl (RAMAlphabet.decode A) (by intro b; rfl) h) (fun _ : RAMAlphabet.Reg A => [])
  have ht := Code.transfer_exec (Sum.inl output) (Sum.inr (.inl 0 : RAMAlphabet.Reg A)) (by simp)
    (.inl false : Letter A) (Sum.elim (Code.listMap Sum.inl out) (fun _ : RAMAlphabet.Reg A => []))
  have hf := Code.Exec.seq hc ht
  simp only [Sum.elim_inl,Sum.elim_inr] at hf
  have he : Function.update
      (Function.update (Sum.elim (Code.listMap Sum.inl out) (fun _ : RAMAlphabet.Reg A => [])) (.inl output) [])
        (.inr (.inl 0)) (((Code.listMap Sum.inl out) output).reverse++[])=
      Sum.elim (Function.update (Code.listMap Sum.inl out) output []) (RAMAlphabet.inputState A ys) := by
    funext r
    cases r with
    | inl r =>
      rw [Function.update_of_ne (show (Sum.inl r : Reg A K)≠.inr (.inl 0) from Sum.inl_ne_inr)]
      simp only [Function.update_apply,Sum.inl.injEq,Sum.elim_inl]
    | inr r =>
      simp only [Function.update_apply,Sum.inr.injEq,Sum.inr_ne_inl,ite_false,Sum.elim_inr,
        RAMAlphabet.inputState,Code.listMap,ho,List.map_reverse,List.reverse_reverse,List.append_nil]
      by_cases hr : r=(.inl 0 : RAMAlphabet.Reg A)
      · simp only [ite_eq_left hr]
      · simp only [ite_eq_right hr]
  rw [he] at hf
  simpa only [prelude,Code.listMap,Sum.elim_inl,Sum.elim_inr,ho,List.length_map,List.length_reverse] using hf
 theorem code_exec (c : Code K Bool) (input output : K) (n : ℕ) (w ys : List Bool)
    {t out} (he : c.Exec (fun r => if r=input then w else []) t out) (ho : out output=ys.reverse)
    (hfit : ys.length ≤ A.width.bits n*2^(A.width.bits n)) (hh : A.halts n ys) :
    ∃u  ≤ t+5*ys.length+RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)+1,∃last b,
      (code A c output (A.width.bits n)).Exec (fun r => if r=.inl input then w.map Sum.inl else []) u last ∧
      answer A (tops last)=(!b) ∧ (b=true ↔ A.accepts n ys) := by
  obtain ⟨v,hv,b,last,hg,ha,hb⟩ := RAMAlphabet.program_exec A n ys hfit hh
  have hg' : (RAMAlphabet.program A (A.width.bits n)).Exec (RAMAlphabet.inputState A ys) v last := Code.Exec.of_decEq hg
  have hf := Code.Exec.seq (prefix_exec A c output he ys ho)
    (Code.relabel_inr_exec hg'  (Function.update (Code.listMap Sum.inl out) output []))
  have hs : Sum.elim (Code.listMap (Sum.inl : Bool → Letter A) (fun r => if r=input then w else []))
      (fun _ : RAMAlphabet.Reg A => [])=(fun r => if r=.inl input then w.map Sum.inl else []) := by
    funext r
    cases r with
    | inl r =>
      by_cases hr : r=input
      · simp only [Code.listMap,Sum.elim_inl,Sum.inl.injEq,ite_eq_left hr]
      · simp only [Code.listMap,Sum.elim_inl,Sum.inl.injEq,ite_eq_right hr,List.map_nil]
    | inr r => simp only [Sum.elim_inr,Sum.inr_ne_inl,ite_false]
  rw [hs] at hf
  refine ⟨t+(5*ys.length+1)+v,by omega,_,b,hf,?_,hb⟩
  simp only [answer,tops,Sum.elim_inr,ha,List.head?_cons,Option.map_some,Option.getD_some,RAMAlphabet.decode]
variable [Fintype K]
def oneTape (c : Code K Bool) (input output : K) (n : ℕ) : OneTape :=
  (code A c output (A.width.bits n)).haltOneTape (.inl input) Sum.inl (answer A)
 theorem correct (c : Code K Bool) (input output : K) (n : ℕ) (w ys : List Bool)
    {t out} (he : c.Exec (fun r => if r=input then w else []) t out) (ho : out output=ys.reverse)
    (hfit : ys.length ≤ A.width.bits n*2^(A.width.bits n)) (hh : A.halts n ys) :
    (oneTape A c input output n).toTM.halts w ∧
    (oneTape A c input output n).toTM.time w ≤
      8*(Fintype.card K+Fintype.card (RAMAlphabet.Reg A)+1)*
        (w.length+t+5*ys.length+RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)+3)^2 ∧
    ((oneTape A c input output n).toTM.accepts w ↔ ¬A.accepts n ys) := by
  obtain ⟨u,hu,last,b,hc,ha,hb⟩ := code_exec A c input output n w ys he ho hfit hh
  obtain ⟨ht,htime,hans⟩ := Code.haltOneTape_correct (code A c output (A.width.bits n)) (.inl input) Sum.inl (answer A) w hc
  refine ⟨ht,htime.trans ?_,hans.trans ?_⟩
  · simp only [Reg,Fintype.card_sum]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  · rw [ha]
    cases b <;> simp_all
 omit [DecidableEq K] [Fintype K] in
 theorem code_size (c : Code K Bool) (output : K) (w : ℕ) :
    (code A c output w).controlSize=c.controlSize+(RAMAlphabet.program A w).controlSize+5 := by
  simp only [code,prelude,Code.controlSize,Code.relabel_controlSize,Code.mapLetters_controlSize,Code.transfer]
  omega
end
end WLTime.RAMConsumer

namespace WLTime.OneTape.Symbolic.RAMWriter
open TypedStack
open scoped Classical
noncomputable section
variable (U : OneTape) (d q : ℕ) (A : RAM)
def consumer (n : ℕ) : OneTape :=
  RAMConsumer.oneTape A (FullWriter.program U d q n).code (.inr FullWriter.Reg.word) (.inr FullWriter.Reg.output) n
def consumerFactor : ℕ := 8*(FullWriter.scratchBound U d q+4+Fintype.card (RAMAlphabet.Reg A)+1)
 theorem correct (n : ℕ) (w : List Bool) (hm : 1 ≤ w.length) (hr : 2 ≤ d+q)
    (hn : baseOrder U d q w.length ≤ n)
    (ys : List Bool) (hys : ys=encodePair (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
      (pairGraph U d q hr w (n-baseOrder U d q w.length) 1))
    (hh : A.halts n ys) :
    (consumer U d q A n).toTM.halts w ∧
    (consumer U d q A n).toTM.time w ≤ consumerFactor U d q A*
      (w.length+FullWriter.budget U d q n w.length+5*ys.length+
        RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)+3)^2 ∧
    ((consumer U d q A n).toTM.accepts w ↔ ¬A.accepts n ys) := by
  have hgn : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,Nat.add_sub_of_le hn]
  have hfit := A.input_fits _ (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
    (pairGraph U d q hr w (n-baseOrder U d q w.length) 1)
  have hfit' : ys.length ≤ A.width.bits n*2^(A.width.bits n) := by
    simpa only [hys,hgn] using hfit
  obtain ⟨t,ht,out,he,ho⟩ := FullWriter.code_correct U d q n w hm hr hn
  rw [←hys] at ho
  have hc := RAMConsumer.correct A (FullWriter.program U d q n).code (.inr FullWriter.Reg.word) (.inr FullWriter.Reg.output) n w ys he ho hfit' hh
  refine ⟨hc.1,hc.2.1.trans ?_,hc.2.2⟩
  have hs := FullWriter.scratch_le U d q n
  rw [Fintype.card_sum,Fintype.card_fin,FullWriter.card_reg]
  exact Nat.mul_le_mul (by unfold consumerFactor; omega) (Nat.pow_le_pow_left (by omega) 2)
 def tapesBound : ℕ := FullWriter.scratchBound U d q+4+Fintype.card (RAMAlphabet.Reg A)
 def alphabetBound : ℕ := 3+2*(3+Fintype.card (RAMAlphabet.Letter A))^tapesBound U d q A
 def ramSize : ℕ := Classical.choose (RAMAlphabet.program_linear A)
 theorem ramSize_spec (w : ℕ) : (RAMAlphabet.program A w).controlSize ≤ ramSize A*(w+1) :=
  Classical.choose_spec (RAMAlphabet.program_linear A) w
 def statesBound : ℕ := 3+14*(tapesBound U d q A+1)*(3+Fintype.card (RAMAlphabet.Letter A))*
    (FullWriter.syntaxBound U d q+ramSize A+7)*(3+Fintype.card (RAMAlphabet.Letter A))^tapesBound U d q A
 theorem consumer_alphabet (n : ℕ) : (consumer U d q A n).symbols ≤ alphabetBound U d q A := by
  unfold consumer RAMConsumer.oneTape Code.haltOneTape
  rw [StackMachine.Machine.compile_symbols]
  change 3+2*((2+Fintype.card (RAMAlphabet.Letter A))+1)^Fintype.card
    (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) ≤ _
  have hreg : Fintype.card (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) =
      (FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A) := by
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,FullWriter.card_reg]
  rw [hreg]
  have hs := FullWriter.scratch_le U d q n
  unfold alphabetBound tapesBound
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [show 2+Fintype.card (RAMAlphabet.Letter A)+1=3+Fintype.card (RAMAlphabet.Letter A) by omega]
  exact Nat.pow_le_pow_right (by omega) (by omega)
 theorem consumer_states (n : ℕ) :
    (consumer U d q A n).states ≤ statesBound U d q A*((Nat.digits 2 n).length+A.width.bits n+2) := by
  have h := StackMachine.Machine.compile_states_bound
    (Code.haltMachine (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n))
      (.inl (.inr FullWriter.Reg.word)) Sum.inl (RAMConsumer.answer A)).compile
  change (consumer U d q A n).states ≤ 3+14*(Fintype.card
    (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg))+1)*
    (2+Fintype.card (RAMAlphabet.Letter A)+1)*
    (Fintype.card (Code.HaltState (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n)))+1)*
    (2+Fintype.card (RAMAlphabet.Letter A)+1)^Fintype.card
      (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) at h
  have hreg : Fintype.card (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) =
      (FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A) := by
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,FullWriter.card_reg]
  rw [hreg] at h
  have hstate : Fintype.card (Code.HaltState (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n))) =
      (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n)).controlSize+1 := by
    rw [Fintype.card_sum,Code.card_state,Fintype.card_unit]
  rw [hstate,RAMConsumer.code_size] at h
  let Y := (Nat.digits 2 n).length+A.width.bits n+2
  let B := 3+Fintype.card (RAMAlphabet.Letter A)
  have hK : (FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A) ≤ tapesBound U d q A := by
    have hs := FullWriter.scratch_le U d q n
    unfold tapesBound; omega
  have hq : (FullWriter.program U d q n).code.controlSize+(RAMAlphabet.program A (A.width.bits n)).controlSize+5+1+1 ≤
      (FullWriter.syntaxBound U d q+ramSize A+7)*Y := by
    have hs := FullWriter.syntax_le U d q n
    have hr := ramSize_spec A (A.width.bits n)
    dsimp only [Y]
    nlinarith only [hs,hr]
  have hp : B^((FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A)) ≤ B^tapesBound U d q A :=
    Nat.pow_le_pow_right (by dsimp [B]; omega) hK
  rw [show 2+Fintype.card (RAMAlphabet.Letter A)+1=B by dsimp [B]; omega] at h
  have ht := Nat.mul_le_mul_right B (Nat.mul_le_mul_left 14 (Nat.add_le_add_right hK 1))
  have hz := Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul ht hq) hp) 3
  have hh := h.trans hz
  change (consumer U d q A n).states ≤ statesBound U d q A*Y
  unfold statesBound
  change (consumer U d q A n).states ≤ (3+14*(tapesBound U d q A+1)*B*(FullWriter.syntaxBound U d q+ramSize A+7)*B^tapesBound U d q A)*Y
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  nlinarith only [hh,hY]
end
end WLTime.OneTape.Symbolic.RAMWriter

namespace WLTime.Numeric
 theorem ram_consumer_small (m a writer len time ram factor : ℕ) (hm : 8 ≤ m)
    (hb : writer ≤ m^2400) (hl : len ≤ m^20) (ht : time ≤ m^(8*a))
    (hr : ram ≤ m*(len+time+1)^2) (hf : factor ≤ m) :
    factor*(m+writer+5*len+ram+3)^2 ≤ m^(2*max 2400 (16*a+45)+3) := by
  let E := max 20 (8*a)
  let D := max 2400 (16*a+45)
  have hle : len ≤ m^E := hl.trans (pow_mono m 20 E (by omega) (le_max_left _ _))
  have hte : time ≤ m^E := ht.trans (pow_mono m (8*a) E (by omega) (le_max_right _ _))
  have hsum := sum_le_pow (by omega : 2 ≤ m) hle hte
  have hone : 1 ≤ m^(E+1) := one_le_pow₀ (by omega)
  have hsum' : len+time+1 ≤ m^(E+2) := by
    simpa only [show E+1+1=E+2 by omega] using sum_le_pow (by omega : 2 ≤ m) hsum hone
  have hram : ram ≤ m^(16*a+45) := by
    calc
      _ ≤ m*(len+time+1)^2 := hr
      _ ≤ m*(m^(E+2))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum' 2)
      _=m^(2*E+5) := by rw [←pow_mul,←pow_succ']; congr 1; omega
      _ ≤ m^(16*a+45) := pow_mono m _ _ (by omega) (by dsimp [E]; omega)
  have h5 : 5*len ≤ m^21 := by
    have h := Nat.mul_le_mul (show 5 ≤ m by omega) hl
    simpa only [pow_succ'] using h
  have hmD : m ≤ m^D := Nat.le_self_pow (by dsimp [D]; omega) m
  have hwD : writer ≤ m^D := hb.trans (pow_mono m 2400 D (by omega) (le_max_left _ _))
  have hlD : 5*len ≤ m^D := h5.trans (pow_mono m 21 D (by omega) (by dsimp [D]; omega))
  have hrD : ram ≤ m^D := hram.trans (pow_mono m (16*a+45) D (by omega) (le_max_right _ _))
  have h3D : 3 ≤ m^D := (by omega : 3 ≤ m).trans hmD
  have hbase : m+writer+5*len+ram+3 ≤ m^(D+1) := by
    rw [pow_succ]
    nlinarith only [hmD,hwD,hlD,hrD,h3D,hm]
  calc
    _ ≤ m*(m^(D+1))^2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hbase 2)
    _=m^(2*D+3) := by rw [←pow_mul,←pow_succ']; congr 1; omega
end WLTime.Numeric

namespace WLTime.OneTape.Symbolic.RAMWriter
open scoped Classical
noncomputable section
variable (A : RAM)
def widthFactor : ℕ := 10*(A.width.bound+1)
 theorem width_small (n m : ℕ) (hm : 2 ≤ m) (hn : n ≤ m^8) :
    A.width.bits n+1 ≤ widthFactor A*((Nat.digits 2 m).length+1) := by
  have hm8 : m ≤ m^8 := Nat.le_self_pow (by decide) m
  have hnm : n+2 ≤ m^9 := by
    simpa using Numeric.sum_le_pow hm hn (show 2 ≤ m^8 by omega)
  have hd := Numeric.digits_polynomial (n+2) m 9 (by decide) hnm
  have he : Nat.log2 (n+2)+1=(Nat.digits 2 (n+2)).length := by
    rw [Nat.length_digits 2 (n+2) (by decide) (by omega),Nat.log2_eq_log_two]
  have hw := A.width.logarithmic n
  rw [he] at hw
  have hx := Nat.mul_le_mul_left A.width.bound hd
  unfold widthFactor
  nlinarith only [hw,hx]
 theorem word_cost_small : ∃m₀,∀m ≥ m₀,∀n ≤ m^8,
    RAMAlphabet.budgetConstant A*(A.width.bits n+1)^RAMAlphabet.exponent A ≤ m := by
  obtain ⟨m₀,hm₀⟩ := Numeric.polylog_sublinear
    (RAMAlphabet.budgetConstant A*(widthFactor A)^RAMAlphabet.exponent A) (RAMAlphabet.exponent A)
  refine ⟨m₀+2,?_⟩
  intro m hm n hn
  have hw := width_small A n m (by omega) hn
  calc
    _ ≤ RAMAlphabet.budgetConstant A*(widthFactor A*((Nat.digits 2 m).length+1))^RAMAlphabet.exponent A :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw _)
    _=(RAMAlphabet.budgetConstant A*(widthFactor A)^RAMAlphabet.exponent A)*((Nat.digits 2 m).length+1)^RAMAlphabet.exponent A := by rw [mul_pow]; ring
    _ ≤ m := hm₀ m (by omega)
variable (U : OneTape) (d q : ℕ)
 theorem designation_small : ∃m₀,∀m ≥ m₀,∀n ≤ m^8,
    (Diagonal.designation (consumer U d q A n)).length ≤ m := by
  let K := statesBound U d q A+alphabetBound U d q A+3
  let F := 9+widthFactor A
  obtain ⟨m₀,hm₀⟩ := Numeric.polylog_sublinear (13*(K*F)^3) 3
  refine ⟨m₀+2,?_⟩
  intro m hm n hn
  let Y := (Nat.digits 2 n).length+A.width.bits n+2
  let B := K*Y
  have hd := Numeric.digits_polynomial n m 8 (by decide) hn
  have hw := width_small A n m (by omega) hn
  have hY : Y ≤ F*((Nat.digits 2 m).length+1) := by dsimp [Y,F]; nlinarith only [hd,hw]
  have hq : (consumer U d q A n).states ≤ B :=
    (consumer_states U d q A n).trans (Nat.mul_le_mul_right _ (by dsimp [K]; omega))
  have hg : (consumer U d q A n).symbols ≤ B := by
    have h := consumer_alphabet U d q A n
    dsimp [B,K,Y]
    nlinarith
  have hB : 3 ≤ B := by dsimp [B,K,Y]; nlinarith
  calc
    _ ≤ 13*B^3 := Diagonal.designation_upper _ B hq hg hB
    _ ≤ 13*(K*F*((Nat.digits 2 m).length+1))^3 := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have h := Nat.mul_le_mul_left K hY
      simpa only [B,Nat.mul_assoc] using h
    _=(13*(K*F)^3)*((Nat.digits 2 m).length+1)^3 := by ring
    _ ≤ m := hm₀ m (by omega)
end
end WLTime.OneTape.Symbolic.RAMWriter

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem diagonal_graph_contradiction (s d q k m pad : ℕ) (c : Convention) (D : OneTape)
    (w z : List Bool) (hw : w=Diagonal.designation D++z) (hlen : w.length=m)
    (hk : k=d+q+conventionShift c) (hm : 128 ≤ m) (hs : 1 ≤ s)
    (hd : d=3*s+6) (hq : d+3 ≤ q) (hr : 2 ≤ d+q)
    (hfit : (Diagonal.designation D).length ≤ m)
    (hUfac : 8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2 ≤ m)
    (hsm : 18*s ≤ m) (hhalt : D.toTM.halts w) (htime : D.toTM.time w ≤ m^s)
    (hpairD : D.toTM.accepts w ↔ ¬Equivalent c k
      (pairGraph (Universal.machine s) d q hr w pad 0)
      (pairGraph (Universal.machine s) d q hr w pad 1)) : False := by
  let U := Universal.machine s
  have hU := Universal.machine_correct s D z (by rw [←hw,hlen]; omega)
  rw [←hw] at hU
  have hUt : U.toTM.time w ≤ w.length^d-1 := by
    apply hU.2.1.trans
    rw [hlen]
    apply (Universal.timeBound_small s D hfit (by omega) hs hsm hUfac).trans
    simpa only [hd] using time_window m s (by omega) hs
  have hwin : 2*(w.length^d-1)+w.length+2<w.length^(q+1) := by
    rw [hlen]; exact space_window m d q (by omega) (by omega) hq
  have hpair := pair_correct_convention U d q hr w (by rw [hlen]; omega) pad hwin c k hk
  have hUb := Diagonal.bounded_accepts_iff U w (w.length^d-1) hU.1 hUt
  have hEq := hpair.trans (not_congr hUb)
  have hc : D.toTM.accepts w ↔ ¬∃t ≤ m^s,(D.toTM.run w t).state.val=1 := by
    have hh := hpairD.trans (not_congr hEq)
    rw [not_not] at hh
    exact hh.trans (by simpa only [hlen] using hU.2.2)
  exact Diagonal.pointwise_contradiction D w (m^s) hhalt htime hc
end WLTime

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem ram_decides_pair (U : OneTape) (d q k n a : ℕ) (w : List Bool)
    (hr : 2 ≤ d+q) (hbase : baseOrder U d q w.length ≤ n)
    (c : Convention) (p : InputClass) (A : RAM) (hA : Decides (.ram A) c k p)
    (hfast : worstTime (.ram A) p n ≤ n^a) :
    let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
    let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
    let ys := encodePair G H
    A.halts n ys ∧ A.time n ys ≤ n^a ∧ (A.accepts n ys ↔ Equivalent c k G H) := by
  dsimp only
  let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
  let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
  let ys := encodePair G H
  have hgn : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,Nat.add_sub_of_le hbase]
  have hprom : p.contains G H := promised_pair U d q hr w _ p
  have hdec := hA _ G H hprom
  change A.halts _ ys ∧ (A.accepts _ ys ↔ Equivalent c k G H) at hdec
  have hhalt : A.halts n ys := by simpa only [hgn] using hdec.1
  have haccept : A.accepts n ys ↔ Equivalent c k G H := by
    have he : A.accepts n ys=A.accepts (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length ys :=
      congrArg (fun j => A.accepts j ys) hgn.symm
    rw [he]
    exact hdec.2
  have htime : A.time n ys ≤ n^a := by
    have ht := worstTime_ge (.ram A) p G H hprom
    change A.time _ ys ≤ worstTime (.ram A) p _ at ht
    rw [hgn] at ht
    exact ht.trans hfast
  exact ⟨hhalt,htime,haccept⟩
 theorem ram_pointwise (s d q k a n m : ℕ) (c : Convention) (p : InputClass) (A : RAM)
    (hA : Decides (.ram A) c k p) (hk : k=d+q+conventionShift c)
    (hm : 128 ≤  m) (hs : 1 ≤  s) (hd : d=3*s+6) (hq : d+3 ≤  q)
    (ha : 2*max 2400 (16*a+45)+3 ≤  s)
    (hbase : baseOrder (Universal.machine s) d q m ≤  n) (hn : n ≤  m^8)
    (hfit : (Diagonal.designation (RAMWriter.consumer (Universal.machine s) d q A n)).length ≤  m)
    (hC : coefficient (Universal.machine s) d q (d+q+2) ≤  m)
    (hcharge : (body (Universal.machine s) d q).charge ≤  m)
    (hfactor : RAMWriter.consumerFactor (Universal.machine s) d q A ≤  m)
    (hword : RAMAlphabet.budgetConstant A*(A.width.bits n+1)^RAMAlphabet.exponent A ≤ m)
    (hUfac : 8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2 ≤  m)
    (hsm : 18*s ≤  m) :
    ¬worstTime (.ram A) p n ≤  n^a := by
  intro hfast
  let U := Universal.machine s
  let D := RAMWriter.consumer U d q A n
  let z := List.replicate (m-(Diagonal.designation D).length) false
  let w := Diagonal.designation D++z
  have hlen : w.length=m := by
    dsimp [w,z]
    rw [List.length_append,List.length_replicate,Nat.add_sub_of_le hfit]
  have hr : 2 ≤  d+q := by omega
  let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
  let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
  let ys := encodePair G H
  obtain ⟨hhalt,htime,haccept⟩ := ram_decides_pair U d q k n a w hr
    (by simpa only [hlen] using hbase) c p A hA hfast
  have hprod := RAMWriter.correct U d q A n w (by rw [hlen]; omega) hr
    (by simpa only [hlen] using hbase) ys rfl hhalt
  have hy : ys.length ≤  m^20 := by
    have hy := input_length U d q n w hr (by simpa only [hlen] using hbase)
    exact hy.le.trans (Numeric.input_small n m (by omega) hn)
  have hb : budget U d q n w.length ≤  m^2400 := by
    rw [hlen]
    simpa only [budget,encodeNat_length] using
      Numeric.writer_small (coefficient U d q (d+q+2)) (body U d q).charge n m hm hC hcharge hn
  have hv : A.time n ys ≤  m^(8*a) := by
    calc
      _ ≤  n^a := htime
      _ ≤ (m^8)^a := Nat.pow_le_pow_left hn a
      _=m^(8*a) := (pow_mul m 8 a).symm
  have hDtime : D.toTM.time w ≤  m^s := by
    have hramb : RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys) ≤ m*(ys.length+A.time n ys+1)^2 :=
      (RAMAlphabet.budget_bound A _ _ _).trans (Nat.mul_le_mul_right _ hword)
    have hbnd := Numeric.ram_consumer_small m a (budget U d q n w.length) ys.length (A.time n ys)
      (RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)) (RAMWriter.consumerFactor U d q A)
      (by omega) hb hy hv hramb hfactor
    have ht := hprod.2.1
    rw [hlen] at ht hbnd
    exact ht.trans (hbnd.trans (Nat.pow_le_pow_right (by omega) ha))
  have heq : D.toTM.accepts w ↔ ¬Equivalent c k G H :=
    hprod.2.2.trans (not_congr haccept)
  exact diagonal_graph_contradiction s d q k m (n-baseOrder U d q w.length) c D w z rfl hlen
    hk hm hs hd hq hr hfit hUfac hsm hprod.1 hDtime heq
end WLTime

end OAI
