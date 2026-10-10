import OAI.Computability.WeisfeilerLeman.Interpreter

namespace OAI

universe uK

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

def reverseInto (a b : K) : Program K := ofCode (Code.transfer a b false)

theorem reverseInto_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (reverseInto a b).Exec s (5*(s a).length+1)
      (Function.update (Function.update s a []) b ((s a).reverse++s b)) :=
  ofCode_exec (Code.transfer_exec a b hab false s)

def shift (a b : K) : Program K :=
  ofCode (.seq (.pushDyn b (fun v => (v a).getD false)) (.pop a))

theorem shift_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (shift a b).Exec s 4
      (Function.update (Function.update s b ((s a).headD false::s b)) a (s a).tail) := by
  apply ofCode_exec
  have he := Code.Exec.seq (Code.Exec.pushDyn s b (fun v => (v a).getD false)) (Code.Exec.pop _ a)
  simpa [Function.update_of_ne hab,tops] using he

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def shiftPair (p : List Bool × List Bool) := (p.1.tail,p.1.headD false::p.2)

theorem shiftPair_prefix (xs ys zs : List Bool) :
    shiftPair^[xs.length] (xs++ys,zs)=(ys,xs.reverse++zs) := by
  induction xs generalizing zs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change shiftPair^[xs.length] (xs++ys,x::zs)=_
    rw [ih,List.reverse_cons,List.append_assoc]
    rfl

def takeDescription : Program Reg :=
  Program.seq (Program.repeatN index (Program.shift search temp)) (Program.reverseInto temp tab)

theorem takeDescription_exec (xs ys : List Bool) (s : Stacks Reg Bool)
    (hs : s search=xs++ys) (hi : s index=numeral xs.length)
    (ht : s temp=[]) (hb : s tab=[]) :
    ∃t≤24*xs.length+4,takeDescription.Exec s t
      (Function.update (Function.update s search ys) tab xs) := by
  let enc (p : List Bool × List Bool) := Function.update (Function.update s search p.1) temp p.2
  have hc (p) : (Program.shift search temp).Exec (enc p) 4 (enc (shiftPair p)) := by
    have he := Program.shift_exec search temp (by decide) (enc p)
    convert he using 1
    funext r; cases r <;> simp [enc,shiftPair]
  have hi' : enc (xs++ys,[]) index=numeral xs.length := by simp [enc,hi]
  obtain ⟨t,htime,he⟩ := Program.repeat_lift index (Program.shift search temp) shiftPair enc 4 xs.length
    (fun p => ⟨4,le_rfl,hc p⟩) (xs++ys,[]) hi'
  rw [shiftPair_prefix] at he
  have hin : enc (xs++ys,[])=s := by
    funext r; cases r <;> simp [enc,hs,ht]
  rw [hin] at he
  have hr := Program.reverseInto_exec temp tab (by decide) (enc (ys,xs.reverse++[]))
  have hout : Function.update (Function.update (enc (ys,xs.reverse++[])) temp []) tab
      (((enc (ys,xs.reverse++[])) temp).reverse++enc (ys,xs.reverse++[]) tab)=
      Function.update (Function.update s search ys) tab xs := by
    funext r; cases r <;> simp [enc,hb,ht]
  rw [hout] at hr
  have hf := Program.seq_exec he hr
  refine ⟨_,?_,hf⟩
  simp only [enc,Function.update_self,List.append_nil,List.length_reverse]
  omega

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def bitValue : Bool → ℕ | false => 1 | true => 2

@[simp] theorem fields_append (xs ys : List ℕ) : fields (xs++ys)=fields xs++fields ys :=
  List.flatMap_append

def tapeBody : Program Reg :=
  Program.seq (Program.push right false) <|
  Program.seq (Program.push right true) <|
  Program.seq (Program.branch (UnaryPrograms.isTrue temp) (Program.push right true) Program.skip) <|
  Program.seq (Program.pop temp) (Program.push base true)

def tapeLoop : Program Reg := Program.loop (Code.nonempty temp) tapeBody

theorem tapeBody_exec (s : Stacks Reg Bool) (b : Bool) (xs : List Bool) (hs : s temp=b::xs) :
    ∃t≤11,tapeBody.Exec s t
      (Function.update (Function.update (Function.update s right (tile (bitValue b)++s right))
        temp xs) base (true::s base)) := by
  let a := Function.update s right (false::s right)
  let c := Function.update a right (true::a right)
  have h1 := Program.push_exec right false s
  have h2 := Program.push_exec right true a
  cases b with
  | false =>
    have hb := Program.branch_false (p:=Program.push right true) (test:=UnaryPrograms.isTrue temp)
      (by simp [UnaryPrograms.isTrue,tops,c,a,hs]) (Program.skip_exec c)
    have h3 := Program.pop_exec temp c
    have h4 := Program.push_exec base true (Function.update c temp (c temp).tail)
    have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec hb (Program.seq_exec h3 h4)))
    refine ⟨10,by omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [c,a,tile,bitValue,numeral,hs]
  | true =>
    have hb := Program.branch_true (q:=Program.skip) (test:=UnaryPrograms.isTrue temp)
      (by simp [UnaryPrograms.isTrue,tops,c,a,hs]) (Program.push_exec right true c)
    let d := Function.update c right (true::c right)
    have h3 := Program.pop_exec temp d
    have h4 := Program.push_exec base true (Function.update d temp (d temp).tail)
    have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec hb (Program.seq_exec h3 h4)))
    refine ⟨11,by omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [d,c,a,tile,bitValue,numeral,hs]

theorem tapeLoop_exec (xs : List Bool) (s : Stacks Reg Bool) (hs : s temp=xs) :
    ∃t≤12*xs.length+1,tapeLoop.Exec s t
      (Function.update (Function.update (Function.update s temp []) right
        (fields (xs.reverse.map bitValue)++s right)) base (numeral xs.length++s base)) := by
  induction xs generalizing s with
  | nil =>
    have he := Program.loop_false (p:=tapeBody) (test:=Code.nonempty temp) (s:=s)
      (by simp [Code.nonempty,tops,hs])
    refine ⟨1,by simp,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [hs,fields,numeral]
  | cons b xs ih =>
    let a := Function.update (Function.update (Function.update s right (tile (bitValue b)++s right))
      temp xs) base (true::s base)
    obtain ⟨t,ht,hb⟩ := tapeBody_exec s b xs hs
    obtain ⟨u,hu,hr⟩ := ih a (by simp [a])
    have he := Program.loop_true (test:=Code.nonempty temp)
      (by simp [Code.nonempty,tops,hs]) hb hr
    refine ⟨t+u+1,by simp only [List.length_cons]; omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [a,List.reverse_cons,List.map_append,List.append_assoc,tile]
    rw [numeral_add]
    simp only [numeral,List.replicate_one,List.append_assoc,List.singleton_append]

def inputPrep : Program Reg :=
  Program.seq (Program.copy input search) <|
  Program.seq (Program.reverseInto input temp) tapeLoop

def inputStore (w : List Bool) : Stacks Reg Bool := fun r => if r=input then w else []

def prepared (w : List Bool) : Stacks Reg Bool
  | .search => w
  | .base => numeral w.length
  | .right => fields (w.map bitValue)
  | _ => []

theorem inputPrep_exec (w : List Bool) :
    ∃t≤29*w.length+4,inputPrep.Exec (inputStore w) t (prepared w) := by
  let a := Function.update (inputStore w) search w
  let b := Function.update (Function.update a input []) temp w.reverse
  have h1 : (Program.copy input search).Exec (inputStore w) (12*w.length+2) a := by
    simpa [a,inputStore] using Program.copy_exec input search (by decide) (inputStore w)
  have h2 : (Program.reverseInto input temp).Exec a (5*w.length+1) b := by
    simpa [b,a,inputStore] using Program.reverseInto_exec input temp (by decide) a
  obtain ⟨t,ht,h3⟩ := tapeLoop_exec w.reverse b (by simp [b])
  have hout : Function.update (Function.update (Function.update b temp []) right
      (fields (w.reverse.reverse.map bitValue)++b right)) base (numeral w.reverse.length++b base)=prepared w := by
    funext r; cases r <;> simp [b,a,inputStore,prepared]
  rw [hout] at h3
  have he := Program.seq_exec h1 (Program.seq_exec h2 h3)
  refine ⟨_,?_,he⟩
  simp only [List.length_reverse] at ht
  omega

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def initialConfig (M : OneTape) (w : List Bool) : Config M :=
  (⟨0,by have := M.states_ge; omega⟩,⟨[],w.map M.toTM.symbol⟩)

@[simp] theorem symbol_val (M : OneTape) (b : Bool) : (M.toTM.symbol b).val=bitValue b := by
  cases b <;> rfl

@[simp] theorem map_symbols_val (M : OneTape) (w : List Bool) :
    (w.map M.toTM.symbol).map Fin.val=w.map bitValue := by
  simp only [List.map_map,Function.comp_def,symbol_val]

def parseProgram : Program Reg :=
  Program.seq (Program.read search index) <|
  Program.seq takeDescription <|
  Program.seq (Program.clear search) <|
  Program.seq (Program.clear index) <|
  Program.seq (skipField tab) (Program.read tab alpha)

def initProgram : Program Reg := Program.seq inputPrep parseProgram

theorem parseProgram_exec (M : OneTape) (z : List Bool) :
    ∃ t ≤ 32*(Diagonal.description M).length+3*z.length+3*M.states+5*M.symbols+15,
      parseProgram.Exec (prepared (Diagonal.designation M++z)) t
        (encode M (Diagonal.designation M++z).length (initialConfig M (Diagonal.designation M++z))) := by
  let ds := Diagonal.description M
  let w := Diagonal.designation M++z
  let a := Function.update (Function.update (prepared w) search (ds++z)) index (numeral ds.length)
  let b := Function.update (Function.update a search z) tab ds
  let c := Function.update b search []
  let d := Function.update c index []
  let e := Function.update d tab (Diagonal.unary M.symbols++Diagonal.tableBits (Diagonal.raw M).table)
  have h1 : (Program.read search index).Exec (prepared w) (5*ds.length+3) a := by
    simpa [a,prepared,w,Diagonal.designation,unary_tile,List.append_assoc,ds]
      using Program.read_exec search index (by decide) (prepared w)
  obtain ⟨t2,ht2,h2⟩ := takeDescription_exec ds z a (by simp [a]) (by simp [a])
    (by simp [a,prepared]) (by simp [a,prepared])
  change takeDescription.Exec a t2 b at h2
  have h3 : (Program.clear search).Exec b (3*z.length+1) c := by
    simpa [c,b] using Program.clear_exec search b
  have h4 : (Program.clear index).Exec c (3*ds.length+1) d := by
    simpa [d,c,b,a] using Program.clear_exec index c
  have h5 : (skipField tab).Exec d (3*M.states+3) e := by
    simpa [e,d,c,b,ds,Diagonal.description,Diagonal.Raw.bits,Diagonal.raw,
      unary_tile,List.append_assoc] using skipField_exec tab d
  have h6 : (Program.read tab alpha).Exec e (5*M.symbols+3)
      (Function.update (Function.update e tab (Diagonal.tableBits (Diagonal.raw M).table)) alpha
        (numeral M.symbols)) := by
    simpa [e,d,c,b,a,prepared,unary_tile] using Program.read_exec tab alpha (by decide) e
  have hout : Function.update (Function.update e tab (Diagonal.tableBits (Diagonal.raw M).table)) alpha
      (numeral M.symbols)=encode M w.length (initialConfig M w) := by
    funext r; cases r <;> simp [e,d,c,b,a,prepared,encode,store,initialConfig,haltFlag,numeral]
    exact congrArg fields (map_symbols_val M w).symm
  rw [hout] at h6
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3
    (Program.seq_exec h4 (Program.seq_exec h5 h6))))
  refine ⟨_,?_,he⟩
  dsimp only [ds] at ht2 ⊢
  omega

theorem initProgram_exec (M : OneTape) (z : List Bool) :
    ∃ t ≤ 64*(Diagonal.designation M++z).length+3*M.states+5*M.symbols+19,
      initProgram.Exec (inputStore (Diagonal.designation M++z)) t
        (encode M (Diagonal.designation M++z).length (initialConfig M (Diagonal.designation M++z))) := by
  obtain ⟨t,ht,h1⟩ := inputPrep_exec (Diagonal.designation M++z)
  obtain ⟨u,hu,h2⟩ := parseProgram_exec M z
  refine ⟨t+u,?_,Program.seq_exec h1 h2⟩
  have hd : (Diagonal.description M).length ≤ (Diagonal.designation M++z).length := by
    simp only [Diagonal.designation,List.length_append]
    omega
  have hz : z.length ≤ (Diagonal.designation M++z).length := by simp
  omega

end WLTime.Universal

namespace WLTime.Universal
open OneTape

def Relative (M : OneTape) (C : M.Config ℤ) (c : Config M) : Prop :=
  c.1=C.state ∧ ∀ z,TapePair.contents (zeroSymbol M) c.2 z=C.tape (C.head+z)

theorem initial_relative (M : OneTape) (w : List Bool) :
    Relative M (M.initial w) (initialConfig M w) := by
  refine ⟨rfl,?_⟩
  intro z
  simp only [TapePair.contents,initialConfig,OneTape.initial,zero_add]
  change (if z<0 then ([] : List (Fin M.symbols)).getD (-z-1).toNat (zeroSymbol M)
    else (w.map M.toTM.symbol).getD z.toNat (zeroSymbol M)) =
    if 0≤z ∧ z.toNat<w.length then M.toTM.symbol (w.getD z.toNat false) else zeroSymbol M
  dsimp only [OneTape.toTM] at *
  by_cases hz : z<0
  · have hn : ¬(0≤z ∧ z.toNat<w.length) := by omega
    rw [ite_eq_left hz,ite_eq_right hn,List.getD_nil]
  · rw [ite_eq_right hz]
    have hz' : 0≤z := by omega
    by_cases hb : z.toNat<w.length
    · rw [ite_eq_left ⟨hz',hb⟩,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hb)]
      rw [List.getElem_map,List.getD_eq_getElem _ _ hb]
    · rw [ite_eq_right (by omega),List.getD_eq_default _ _ (by simp only [List.length_map]; omega)]

theorem next_relative (M : OneTape) (C : M.Config ℤ) (c : Config M) (h : Relative M C c) :
    Relative M (M.step lineShift C) (next M c) := by
  classical
  have ho : c.2.right.headD (zeroSymbol M)=C.tape C.head := by
    simpa only [TapePair.contents_zero,add_zero] using h.2 0
  by_cases hh : C.state.val=1 ∨ C.state.val=2
  · rw [M.step_halted lineShift C hh]
    constructor
    · simp only [next,nextState,h.1,hh,ite_true]
    · simpa only [next,nextTape,h.1,hh,ite_true] using h.2
  · constructor
    · simp only [next,nextState,h.1,hh,ite_false,ho,OneTape.step,OneTape.action]
    · intro z
      simp only [next,nextTape,h.1,hh,ite_false,ho,TapePair.contents_moveWrite]
      rw [h.2]
      simp only [OneTape.step,OneTape.action,hh,ite_false,moveAt_line,Function.update_apply]
      have he : C.head+(M.transition C.state (C.tape C.head)).2.2.displacement+z=C.head ↔
          z+(M.transition C.state (C.tape C.head)).2.2.displacement=0 := by omega
      rw [he]
      rw [show C.head+(z+(M.transition C.state (C.tape C.head)).2.2.displacement)=
        C.head+(M.transition C.state (C.tape C.head)).2.2.displacement+z by omega]
      by_cases hp : z+(M.transition C.state (C.tape C.head)).2.2.displacement=0 <;>
        simp only [hp,ite_true,ite_false]

theorem iterate_relative (M : OneTape) (w : List Bool) (t : ℕ) :
    Relative M (M.run lineShift (M.initial w) t) ((next M)^[t] (initialConfig M w)) := by
  induction t with
  | zero => exact initial_relative M w
  | succ t ih =>
    simp only [OneTape.run,Function.iterate_succ_apply'] at *
    exact next_relative M _ _ ih

theorem simulated_state (M : OneTape) (w : List Bool) (t : ℕ) :
    ((next M)^[t] (initialConfig M w)).1.val=(M.toTM.run w t).state.val := by
  have h := (iterate_relative M w t).1
  have ht := congrArg (fun C : M.toTM.Config => C.state.val) (M.embed_run w t)
  exact congrArg Fin.val h |>.trans ht

end WLTime.Universal

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

def inputStacks (k : K) (w : List Bool) : Stacks K Bool := fun j => if j=k then w else []

abbrev FinalState (p : Program K) := p.code.State ⊕ Unit

def finalTransition (p : Program K) (answer : Tops K Bool → Bool) :
    FinalState p → Tops (Fin p.scratch ⊕ K) Bool → Command (Fin p.scratch ⊕ K) Bool (FinalState p)
  | .inl q,v => Command.redirect Sum.inl (.inr ()) (p.code.transition q v)
  | .inr _,v => .halt (answer (v ∘ Sum.inr))

def machine (p : Program K) (k : K) (answer : Tops K Bool → Bool) :
    Machine (Fin p.scratch ⊕ K) Bool (FinalState p) where
  inputStack := .inr k
  inputLetter := id
  initial := .inl p.code.entry
  transition := finalTransition p answer

theorem machine_initial (p : Program K) (k : K) (answer : Tops K Bool → Bool) (w : List Bool) :
    (p.machine k answer).initialConfig w=⟨.inr (.inl p.code.entry),p.ambient (inputStacks k w)⟩ := by
  dsimp only [Machine.initialConfig,machine]
  congr 1
  funext j
  cases j with
  | inl i => simp [ambient]
  | inr i => simp [ambient,inputStacks]

theorem machine_run (p : Program K) (k : K) (answer : Tops K Bool → Bool) (w : List Bool)
    {t out} (h : p.Exec (inputStacks k w) t out) :
    (p.machine k answer).run w (t+1)=⟨.inl (answer (tops out)),p.ambient out⟩ := by
  have he := (Code.exec_finite h).plug Sum.inl (.inr ()) (fun _ _ => rfl)
    (Execution.halt (tr:=finalTransition p answer) (q:=.inr ()) (s:=p.ambient out) rfl)
  rw [Machine.run,machine_initial]
  exact Execution.iterate (p.machine k answer) he

variable [Fintype K]

theorem oneTape_correct (p : Program K) (k : K) (answer : Tops K Bool → Bool) (w : List Bool)
    {t out} (h : p.Exec (inputStacks k w) t out) :
    (p.machine k answer).compile.oneTape.toTM.halts w ∧
    (p.machine k answer).compile.oneTape.toTM.time w ≤
      8*(p.scratch+Fintype.card K+1)*(w.length+t+2)^2 ∧
    ((p.machine k answer).compile.oneTape.toTM.accepts w ↔ answer (tops out)=true) := by
  have hrun := congrArg Config.state (p.machine_run k answer w h)
  have he := (p.machine k answer).oneTape_correct w (t+1) (answer (tops out)) hrun
  simpa only [Fintype.card_sum,Fintype.card_fin,show w.length+(t+1)+1=w.length+t+2 by omega] using he

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack Reg

def boundedProgram (s : ℕ) : Program Reg := Program.seq initProgram (steps s)
def answer (v : Tops Reg Bool) : Bool := v halt != some false

noncomputable def machine (s : ℕ) : OneTape := ((boundedProgram s).machine input answer).compile.oneTape

@[simp] theorem haltFlag_answer (q : ℕ) : ((haltFlag q).head? != some false)=decide (q≠1) := by
  by_cases h1 : q=1
  · simp [haltFlag,h1]
  · by_cases h2 : q=2 <;> simp [haltFlag,h1,h2]

theorem boundedProgram_exec (s : ℕ) (M : OneTape) (z : List Bool)
    (hm : 0 < (Diagonal.designation M++z).length) :
    ∃ t ≤ 64*(Diagonal.designation M++z).length+3*M.states+5*M.symbols+19+
        (stepBound M+18*s)*(Diagonal.designation M++z).length^s,
      (boundedProgram s).Exec (inputStore (Diagonal.designation M++z)) t
        (encode M (Diagonal.designation M++z).length
          ((next M)^[(Diagonal.designation M++z).length^s] (initialConfig M (Diagonal.designation M++z)))) := by
  obtain ⟨t,ht,h1⟩ := initProgram_exec M z
  obtain ⟨u,hu,h2⟩ := steps_exec M (Diagonal.designation M++z).length hm s (initialConfig M (Diagonal.designation M++z))
  exact ⟨t+u,by omega,Program.seq_exec h1 h2⟩

def timeBound (s : ℕ) (M : OneTape) (m : ℕ) : ℕ :=
  8*((boundedProgram s).scratch+Fintype.card Reg+1)*
    (65*m+3*M.states+5*M.symbols+21+(stepBound M+18*s)*m^s)^2

theorem machine_correct (s : ℕ) (M : OneTape) (z : List Bool)
    (hm : 0 < (Diagonal.designation M++z).length) :
    (machine s).toTM.halts (Diagonal.designation M++z) ∧
    (machine s).toTM.time (Diagonal.designation M++z) ≤ timeBound s M (Diagonal.designation M++z).length ∧
    ((machine s).toTM.accepts (Diagonal.designation M++z) ↔
      ¬∃ t ≤ (Diagonal.designation M++z).length^s,
        (M.toTM.run (Diagonal.designation M++z) t).state.val=1) := by
  let w := Diagonal.designation M++z
  obtain ⟨t,ht,he⟩ := boundedProgram_exec s M z hm
  have hc := (boundedProgram s).oneTape_correct input answer w he
  change (machine s).toTM.halts w ∧ (machine s).toTM.time w ≤ timeBound s M w.length ∧
    ((machine s).toTM.accepts w ↔ ¬∃ t ≤ w.length^s, (M.toTM.run w t).state.val=1)
  refine ⟨hc.1,?_,?_⟩
  · apply hc.2.1.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp only [w]
    omega
  · change ((boundedProgram s).machine input answer).compile.oneTape.toTM.accepts w ↔ _
    rw [hc.2.2]
    simp only [answer,tops,encode,store,haltFlag_answer,decide_eq_true_eq]
    rw [simulated_state]
    constructor
    · intro h ⟨u,hu,hacc⟩
      exact h (by rw [M.toTM.run_frozen w (Or.inl hacc) hu]; exact hacc)
    · intro h hacc
      exact h ⟨w.length^s,le_rfl,hacc⟩

end WLTime.Universal

end OAI
