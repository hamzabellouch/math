import OAI.Computability.WeisfeilerLeman.TapePair

namespace OAI

universe uK uA uB

namespace WLTime.TMStack
open TypedStack
variable (M : TM)

theorem execution_halted (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols))
    (h : M.halted C) :
    Execution (transition M) (.inl C.state) (store s) 1 (decide (C.state.val=1)) (store s) := by
  rcases h with ha | hr
  · exact .halt (by simp [transition,ha])
  · have ha : C.state.val≠1 := by omega
    exact .halt (by simp [transition,hr])

theorem simulate (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (t : ℕ)
    (hr : Relative M C s) (ht : M.halted (M.step^[t] C)) :
    ∃ u b out, u ≤ (8*M.tapes+2)*t+1 ∧
      Execution (transition M) (.inl C.state) (store s) u b out ∧
      (b=true ↔ (M.step^[t] C).state.val=1) := by
  induction t generalizing C s with
  | zero => exact ⟨1,_,_,by omega,(execution_halted M) C s ht,by simp⟩
  | succ t ih =>
    by_cases hh : M.halted C
    · have he : M.step^[t+1] C=C := Function.iterate_fixed (by simp [TM.step,hh]) _
      refine ⟨1,_,_,by omega,(execution_halted M) C s hh,?_⟩
      simp only [he,decide_eq_true_eq]
    · let p := M.transition C.state (fun a => C.tape a (C.head a))
      have he : (M.step C).state=p.1 := by simp only [TM.step,hh,ite_false,p]
      obtain ⟨u,b,out,hu,hex,hans⟩ := ih (M.step C) (nextTapes M p s)
        ((next_relative M) hr hh) (by simpa only [Function.iterate_succ_apply] using ht)
      rw [he] at hex
      have hb := (Code.exec_finite ((stepCode_exec M) p s)).plug
        (fun r => Sum.inr (⟨p,r⟩ : (p : Payload M) × (stepCode M p).State)) (.inl p.1)
        (fun _ _ => rfl) hex
      have h1 : C.state.val≠1 := fun hp => hh (Or.inl hp)
      have h2 : C.state.val≠2 := fun hp => hh (Or.inr hp)
      have hf : transition M (.inl C.state) (tops (store s))=
          .next (.inr ⟨p,(stepCode M p).entry⟩) := by
        simp only [transition,h1,h2,ite_false]
        rw [observed M hr]
      refine ⟨_,b,out,?_,Execution.next hf hb,?_⟩
      · have hc := bodyCost_le p.2.2 (List.finRange M.tapes)
        rw [List.length_finRange] at hc
        simp only [Nat.mul_succ]
        omega
      · simpa only [Function.iterate_succ_apply] using hans

def initialTapes (w : List Bool) : Fin M.tapes → TapePair.Tape (Fin M.symbols) :=
  fun a => ⟨[],if a.val=0 then w.map M.symbol else []⟩

theorem initial_relative (w : List Bool) : Relative M (M.initial w) (initialTapes M w) := by
  intro a z
  simp only [TapePair.contents,initialTapes,TM.initial,zero_add]
  by_cases hz : z<0
  · have hz' : ¬0≤z := by omega
    simp only [hz,ite_true,List.getD_nil,hz',false_and,and_false,ite_false]
    rfl
  · have hz' : 0≤z := by omega
    simp only [hz,ite_false,hz']
    by_cases ha : a.val=0
    · simp only [ha,ite_true,true_and]
      by_cases hb : z.toNat<w.length
      · simp only [hb,ite_true,List.getD_eq_getElem (w.map M.symbol) (blank M) (by simpa only [List.length_map] using hb),
          List.getElem_map,List.getD_eq_getElem _ _ hb]
      · have hb' : w.length≤z.toNat := by omega
        simp only [hb,ite_false,List.getD_eq_default (w.map M.symbol) (blank M) (by simpa only [List.length_map] using hb')]
        rfl
    · simp only [ha,ite_false,false_and,List.getD_nil]
      rfl

theorem initial_store (w : List Bool) :
    (machine M).initialConfig w=⟨.inr (.inl (⟨0,by have := M.states_ge; omega⟩ : Fin M.states)),
      store (initialTapes M w)⟩ := by
  simp only [Machine.initialConfig,machine]
  congr 1
  funext ⟨a,b⟩
  have ha : a=⟨0,M.tapes_pos⟩ ↔ a.val=0 := Fin.ext_iff
  cases b <;> simp [store,initialTapes,ha]

theorem machine_correct (w : List Bool) (t : ℕ) (ht : M.halted (M.run w t)) :
    ∃ u b, u≤(8*M.tapes+2)*t+1 ∧ ((machine M).run w u).state=.inl b ∧
      (b=true ↔ (M.run w t).state.val=1) := by
  obtain ⟨u,b,out,hu,hex,hans⟩ := (simulate M) (M.initial w) ((initialTapes M) w) t
    ((initial_relative M) w) ht
  refine ⟨u,b,hu,?_,hans⟩
  have he := hex.iterate (machine M)
  change ((machine M).step^[u] ((machine M).initialConfig w)).state=.inl b
  rw [initial_store M]
  exact congrArg Config.state he

end WLTime.TMStack

namespace WLTime.TMStack
variable (M : TM)
noncomputable def oneTape : OneTape := (machine M).compile.oneTape

theorem oneTape_correct (w : List Bool) (t : ℕ) (ht : M.halted (M.run w t)) :
    (oneTape M).toTM.halts w ∧
      (oneTape M).toTM.time w ≤ 8*(2*M.tapes+1)*
        (w.length+(8*M.tapes+2)*t+2)^2 ∧
      ((oneTape M).toTM.accepts w ↔ M.accepts w) := by
  obtain ⟨u,b,hu,hr,hans⟩ := machine_correct M w t ht
  obtain ⟨hh,hc,ha⟩ := (machine M).oneTape_correct w u b hr
  refine ⟨hh,?_,ha.trans (hans.trans (M.accepts_iff_at_halt w ht).symm)⟩
  calc
    (oneTape M).toTM.time w ≤ 8*(Fintype.card (Fin M.tapes × Bool)+1)*(w.length+u+1)^2 := hc
    _ ≤ 8*(2*M.tapes+1)*(w.length+(8*M.tapes+2)*t+2)^2 := by
      simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm M.tapes 2]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

end WLTime.TMStack

namespace WLTime.TMConsumer
open TypedStack
variable {K : Type uK} [DecidableEq K] (M : TM)
def decode (x : Fin M.symbols) : Bool := decide (x.val=2)
 theorem decode_symbol : Function.LeftInverse (decode M) M.symbol := by
  intro b; cases b <;> simp [decode,TM.symbol]
def boolInput (k : K) (w : List Bool) : Stacks K Bool := fun j => if j=k then w else []
abbrev Reg (M : TM) (K : Type uK) := K ⊕ (Fin M.tapes × Bool)
def tmInput : Fin M.tapes × Bool := (⟨0,M.tapes_pos⟩,true)
def prelude (c : Code K Bool) (output : K) : Code (Reg M K) (Fin M.symbols) :=
  .seq ((c.mapLetters M.symbol (decode M)).relabel Sum.inl)
    (Code.transfer (.inl output) (.inr (tmInput M)) (TMStack.blank M))
abbrev State (c : Code K Bool) (output : K) := (prelude M c output).State ⊕ TMStack.State M
noncomputable instance (c : Code K Bool) (output : K) : Fintype (State M c output) := inferInstanceAs
  (Fintype ((prelude M c output).State ⊕ TMStack.State M))
def transition (c : Code K Bool) (output : K) (answer : Bool → Bool) : State M c output →
    Tops (Reg M K) (Fin M.symbols) → Command (Reg M K) (Fin M.symbols) (State M c output)
  | .inl q,v => Command.redirect Sum.inl (.inr (TMStack.machine M).initial) ((prelude M c output).transition q v)
  | .inr q,v => Command.transport Sum.inr Sum.inr answer (TMStack.transition M q (v ∘ Sum.inr))
def machine (c : Code K Bool) (input output : K) (answer : Bool → Bool) :
    Machine (Reg M K) (Fin M.symbols) (State M c output) where
  inputStack := .inl input
  inputLetter := M.symbol
  initial := .inl (prelude M c output).entry
  transition := transition M c output answer

 theorem prefix_exec (c : Code K Bool) (output : K) {s t out} (h : c.Exec s t out)
    (ys : List Bool) (ho : out output=ys.reverse) :
    (prelude M c output).Exec (Sum.elim (Code.listMap M.symbol s) (fun _ => []))
      (t+(5*ys.length+1))
      (Sum.elim (Function.update (Code.listMap M.symbol out) output [])
        (TMStack.store (TMStack.initialTapes M ys))) := by
  have hc := Code.relabel_inl_exec (Code.mapLetters_exec M.symbol (decode M) (decode_symbol M) h)
    (fun _ : Fin M.tapes × Bool => [])
  have ht := Code.transfer_exec (Sum.inl output) (Sum.inr (tmInput M)) (by simp)
    (TMStack.blank M) (Sum.elim (Code.listMap M.symbol out) (fun _ : Fin M.tapes × Bool => []))
  have hf := Code.Exec.seq hc ht
  have he : Function.update
      (Function.update (Sum.elim (Code.listMap M.symbol out) (fun _ : Fin M.tapes × Bool => [])) (.inl output) [])
        (.inr (tmInput M)) (((Code.listMap M.symbol out) output).reverse++[])=
      Sum.elim (Function.update (Code.listMap M.symbol out) output [])
        (TMStack.store (TMStack.initialTapes M ys)) := by
    funext j; cases j with
    | inl k =>
      by_cases hk : k=output
      · subst k; simp only [Function.update_of_ne Sum.inl_ne_inr,Function.update_self,Sum.elim_inl]
      · simp only [Function.update_of_ne Sum.inl_ne_inr,
          Function.update_of_ne (fun h : Sum.inl k=Sum.inl output => hk (Sum.inl.inj h)),
          Sum.elim_inl,Function.update_of_ne hk]
    | inr k =>
      rcases k with ⟨a,b⟩
      by_cases ha : a=⟨0,M.tapes_pos⟩
      · subst a
        cases b <;> simp only [tmInput,Function.update_apply,Sum.inr.injEq,Prod.mk.injEq,
          true_and,reduceCtorEq,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inr,TMStack.store,
          TMStack.initialTapes,Code.listMap,ho,List.map_reverse,List.reverse_reverse,
          List.append_nil,Bool.false_eq_true]
      · have hv : a.val≠0 := fun hh => ha (Fin.ext hh)
        cases b <;> simp only [tmInput,Function.update_of_ne Sum.inr_ne_inl,
          Function.update_apply,Sum.inr.injEq,Prod.mk.injEq,ha,false_and,ite_false,Sum.elim_inr,
          TMStack.store,TMStack.initialTapes,hv,Bool.false_eq_true,ite_true]
  simp only [Sum.elim_inl,Sum.elim_inr] at hf
  rw [he] at hf
  simpa only [prelude,Code.listMap,ho,List.length_map,List.length_reverse] using hf

 theorem machine_initial (c : Code K Bool) (input output : K) (answer : Bool → Bool) (w : List Bool) :
    (machine M c input output answer).initialConfig w=
      ⟨.inr (.inl (prelude M c output).entry),
        Sum.elim (Code.listMap M.symbol (boolInput input w)) (fun _ => [])⟩ := by
  change Config.mk _ (fun j => if j=Sum.inl input then w.map M.symbol else [])=_
  congr 1
  funext j; cases j with
  | inl k => by_cases hk : k=input <;> simp [Code.listMap,boolInput,hk]
  | inr k => simp

 theorem machine_correct (c : Code K Bool) (input output : K) (answer : Bool → Bool)
    (w ys : List Bool) {t out} (hc : c.Exec (boolInput input w) t out) (ho : out output=ys.reverse)
    (v : ℕ) (hv : M.halted (M.run ys v)) :
    ∃ u b,u≤t+5*ys.length+(8*M.tapes+2)*v+2 ∧
      ((machine M c input output answer).run w u).state=.inl (answer b) ∧
      (b=true ↔ M.accepts ys) := by
  obtain ⟨u,b,last,hu,he,hb⟩ := TMStack.simulate M (M.initial ys) (TMStack.initialTapes M ys) v
    (TMStack.initial_relative M ys) hv
  have htm := he.transport_inr (tr':=transition M c output answer) Sum.inr answer (fun _ _ => rfl)
    (Function.update (Code.listMap M.symbol out) output [])
  have hp := (Code.exec_finite (prefix_exec M c output hc ys ho)).plug Sum.inl
    (.inr (TMStack.machine M).initial) (fun _ _ => rfl) htm
  refine ⟨t+(5*ys.length+1)+u,b,by omega,?_,hb.trans (M.accepts_iff_at_halt ys hv).symm⟩
  have hf := hp.iterate (machine M c input output answer)
  rw [Machine.run,machine_initial]
  exact congrArg Config.state hf

variable [Fintype K]
noncomputable def oneTape (c : Code K Bool) (input output : K) (answer : Bool → Bool) : OneTape :=
  (machine M c input output answer).compile.oneTape
 theorem oneTape_correct (c : Code K Bool) (input output : K) (w ys : List Bool)
    {t out} (hc : c.Exec (boolInput input w) t out) (ho : out output=ys.reverse)
    (v : ℕ) (hv : M.halted (M.run ys v)) :
    (oneTape M c input output not).toTM.halts w ∧
    (oneTape M c input output not).toTM.time w ≤
      8*(Fintype.card K+2*M.tapes+1)*(w.length+t+5*ys.length+(8*M.tapes+2)*v+3)^2 ∧
    ((oneTape M c input output not).toTM.accepts w ↔ ¬M.accepts ys) := by
  obtain ⟨u,b,hu,he,hb⟩ := machine_correct M c input output not w ys hc ho v hv
  obtain ⟨hh,ht,ha⟩ := (machine M c input output not).oneTape_correct w u (!b) he
  refine ⟨hh,?_,ha.trans ?_⟩
  · calc
      _ ≤ 8*(Fintype.card (Reg M K)+1)*(w.length+u+1)^2 := ht
      _ ≤ _ := by
        rw [show Fintype.card (Reg M K)=Fintype.card K+2*M.tapes by
          simp only [Reg,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
          omega]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  · cases b <;> simp_all
end WLTime.TMConsumer

namespace WLTime.StackMachine.Machine
variable (K a q : ℕ)
abbrev ControlCode := Fin 14 × Option (Fin K) × Option (Fin a) × Option (Fin q) × (Fin K → Option (Fin a))
def controlCode : SweepControl K a q → ControlCode K a q
  | .mark => (0,none,none,none,fun _ => none)
  | .seekEnd => (1,none,none,none,fun _ => none)
  | .take => (2,none,none,none,fun _ => none)
  | .bring x => (3,none,some x,none,fun _ => none)
  | .append x => (4,none,some x,none,fun _ => none)
  | .back => (5,none,none,none,fun _ => none)
  | .start z => (6,none,none,some z,fun _ => none)
  | .seek (.peek k z v) => (7,some k,none,some z,v)
  | .seek (.push k x z) => (8,some k,some x,some z,fun _ => none)
  | .seek (.pop k z) => (9,some k,none,some z,fun _ => none)
  | .read k z v => (10,some k,none,some z,v)
  | .returnPeek k z v => (11,some k,none,some z,v)
  | .erase k z => (12,some k,none,some z,fun _ => none)
  | .ret z => (13,none,none,some z,fun _ => none)
def decodeControl (c : ControlCode K a q) : Option (SweepControl K a q) :=
  let (tag,k,x,z,v) := c
  match tag.val with
  | 0 => some .mark
  | 1 => some .seekEnd
  | 2 => some .take
  | 3 => x.map .bring
  | 4 => x.map .append
  | 5 => some .back
  | 6 => z.map .start
  | 7 => do let k←k; let z←z; pure (.seek (.peek k z v))
  | 8 => do let k←k; let x←x; let z←z; pure (.seek (.push k x z))
  | 9 => do let k←k; let z←z; pure (.seek (.pop k z))
  | 10 => do let k←k; let z←z; pure (.read k z v)
  | 11 => do let k←k; let z←z; pure (.returnPeek k z v)
  | 12 => do let k←k; let z←z; pure (.erase k z)
  | _ => z.map .ret
 theorem decode_control (c : SweepControl K a q) : decodeControl K a q (controlCode K a q c)=some c := by
  cases c with
  | seek p => cases p <;> rfl
  | _ => rfl
 theorem control_bound : Fintype.card (SweepControl K a q)≤14*(K+1)*(a+1)*(q+1)*(a+1)^K := by
  have hi : Function.Injective (controlCode K a q) := by
    intro x y h
    apply Option.some.inj
    rw [←decode_control K a q x,←decode_control K a q y,h]
  have h := Fintype.card_le_of_injective _ hi
  simp only [ControlCode,Fintype.card_prod,Fintype.card_fin,Fintype.card_option,Fintype.card_fun] at h
  convert h using 1
  ring_nf

 theorem compile_states_bound (M : StackMachine.Machine) :
    M.oneTape.states≤3+14*(M.count+1)*(M.alphabet+1)*(M.states+1)*(M.alphabet+1)^M.count :=
  Nat.add_le_add_left (control_bound _ _ _) 3
 theorem compile_symbols (M : StackMachine.Machine) :
    M.oneTape.symbols=3+2*(M.alphabet+1)^M.count := by
  change 3+Fintype.card (Bool × (Fin M.count → Option (Fin M.alphabet)))=_
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fun,Fintype.card_option,Fintype.card_fin]
end WLTime.StackMachine.Machine

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {B : Type uB}
 theorem mapLetters_controlSize (f : A → B) (g : B → A) (p : Code K A) :
    (p.mapLetters f g).controlSize=p.controlSize := by
  induction p <;> simp_all [mapLetters,controlSize]
end WLTime.TypedStack.Code

namespace WLTime.OneTape.Symbolic.FullWriter
open TypedStack UnaryPrograms
 theorem consumer_bound (A : TM) (p : Program Reg) (src dst : Reg) (w ys : List Bool)
    (b T : ℕ) (hp : p.scratch ≤ b) {t out} (ht : t ≤ T)
    (he : p.code.Exec (TMConsumer.boolInput (.inr src) w) t out)
    (ho : out (.inr dst)=ys.reverse) (v : ℕ) (hv : A.halted (A.run ys v)) :
    (TMConsumer.oneTape A p.code (.inr src) (.inr dst) not).toTM.halts w ∧
    (TMConsumer.oneTape A p.code (.inr src) (.inr dst) not).toTM.time w ≤
      8*(b+4+2*A.tapes+1)*(w.length+T+5*ys.length+(8*A.tapes+2)*v+3)^2 ∧
    ((TMConsumer.oneTape A p.code (.inr src) (.inr dst) not).toTM.accepts w ↔ ¬A.accepts ys) := by
  have h := TMConsumer.oneTape_correct A p.code (.inr src) (.inr dst) w ys he ho v hv
  refine ⟨h.1,h.2.1.trans ?_,h.2.2⟩
  simp only [Fintype.card_sum,Fintype.card_fin,show Fintype.card Reg=4 from by decide]
  apply Nat.mul_le_mul
  · omega
  · exact Nat.pow_le_pow_left (by omega) 2
end WLTime.OneTape.Symbolic.FullWriter
namespace WLTime.OneTape.Symbolic.FullWriter
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (U : OneTape) (d q : ℕ)
@[simp] theorem card_reg : Fintype.card Reg=4 := by
  decide
@[simp] theorem encodeNat_length (n : ℕ) : (encodeNat n).length=2*(Nat.digits 2 n).length+1 := by
  simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil,List.length_map]
  omega

noncomputable def scratchBound : ℕ := (Program.countLength Reg.word Reg.len).scratch+2+
  ((body U d q).compile rho Reg.word Reg.output).scratch
 theorem scratch_le (n : ℕ) : (program U d q n).scratch ≤ scratchBound U d q := by
  have h := Program.loadDigits_scratch Reg.order (Nat.digits 2 n)
  simp only [program,Program.seqShared,Program.pushes_scratch,scratchBound,Program.loadNat]
  omega
noncomputable def syntaxBound : ℕ :=
  (Program.countLength Reg.word Reg.len).code.controlSize+
  (Program.doubleUnary Reg.order).code.controlSize+10+
  ((body U d q).compile rho Reg.word Reg.output).code.controlSize
 theorem syntax_le (n : ℕ) : (program U d q n).code.controlSize ≤ syntaxBound U d q*((Nat.digits 2 n).length+1) := by
  have h := Program.loadNat_size Reg.order n
  simp only [program,Program.seqShared_size,Program.pushes_size,List.length_reverse,encodeNat_length]
  have he := Nat.le_mul_of_pos_right
    ((Program.countLength Reg.word Reg.len).code.controlSize+
      ((body U d q).compile rho Reg.word Reg.output).code.controlSize+4)
    (show 0 < (Nat.digits 2 n).length+1 by omega)
  dsimp only [syntaxBound]
  nlinarith

noncomputable def consumer (A : TM) (n : ℕ) : OneTape :=
  TMConsumer.oneTape A (program U d q n).code (.inr Reg.word) (.inr Reg.output) not

 theorem code_correct (n : ℕ) (w : List Bool) (hm : 1 ≤ w.length) (hr : 2 ≤ d+q)
    (hn : baseOrder U d q w.length ≤ n) :
    ∃t ≤ budget U d q n w.length,∃out,
      (program U d q n).code.Exec (TMConsumer.boolInput (.inr Reg.word) w) t out ∧
      out (.inr Reg.output)=(encodePair
        (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
        (pairGraph U d q hr w (n-baseOrder U d q w.length) 1)).reverse := by
  obtain ⟨t,ht,out,he,ho⟩ := correct U d q n w hm hr hn
  refine ⟨t,ht,(program U d q n).ambient out,?_,ho⟩
  have hs : (program U d q n).ambient (fun r => if r=Reg.word then w else [])=
      TMConsumer.boolInput (.inr Reg.word) w := by
    funext k; cases k <;> simp [Program.ambient,TMConsumer.boolInput]
  simpa only [Program.Exec,hs] using he

noncomputable def consumerFactor (A : TM) : ℕ := 8*(scratchBound U d q+4+2*A.tapes+1)
 theorem consumer_correct (A : TM) (n : ℕ) (w : List Bool) (hm : 1 ≤ w.length) (hr : 2 ≤ d+q)
    (hn : baseOrder U d q w.length ≤ n)
    (ys : List Bool) (hys : ys = encodePair (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
      (pairGraph U d q hr w (n-baseOrder U d q w.length) 1))
    (v : ℕ) (hv : A.halted (A.run ys v)) :
    (consumer U d q A n).toTM.halts w ∧
    (consumer U d q A n).toTM.time w  ≤
      consumerFactor U d q A*(w.length+budget U d q n w.length+5*ys.length+(8*A.tapes+2)*v+3)^2 ∧
    ((consumer U d q A n).toTM.accepts w ↔ ¬A.accepts ys) := by
  subst ys
  obtain ⟨t,ht,out,he,ho⟩ := code_correct U d q n w hm hr hn
  apply consumer_bound A (program U d q n) Reg.word Reg.output w _
    (scratchBound U d q) (budget U d q n w.length) (scratch_le U d q n) ht he ho v hv

 theorem input_length (n : ℕ) (w : List Bool) (hr : 2 ≤ d+q) (hn : baseOrder U d q w.length ≤ n) :
    (encodePair (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
      (pairGraph U d q hr w (n-baseOrder U d q w.length) 1)).length=
      2*(Nat.digits 2 n).length+1+2*n^2 := by
  have hl : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,Nat.add_sub_of_le hn]
  have hbits {v : ℕ} (G : Graph v) : (matrixBits G).length=v^2 := by
    simp [matrixBits,List.length_flatten,Function.comp_def,pow_two]
  simp only [encodePair,List.length_append,encodeNat_length,hbits,hl]
  omega

end WLTime.OneTape.Symbolic.FullWriter

namespace WLTime.TMConsumer
open TypedStack
variable {K : Type uK} [DecidableEq K] [Fintype K] (M : TM)
 omit [DecidableEq K] [Fintype K] in
 theorem prelude_size (c : Code K Bool) (output : K) :
    (prelude M c output).controlSize=c.controlSize+5 := by
  simp only [prelude,Code.controlSize,Code.relabel_controlSize,Code.mapLetters_controlSize,
    Code.transfer]
 omit [DecidableEq K] [Fintype K] in
 theorem state_card (c : Code K Bool) (output : K) :
    Fintype.card (State M c output)=c.controlSize+5+Fintype.card (TMStack.State M) := by
  rw [Fintype.card_sum,Code.card_state,prelude_size]
end WLTime.TMConsumer

end OAI
