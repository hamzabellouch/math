import OAI.Computability.WeisfeilerLeman.Universal

namespace OAI

universe uK uC

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def motionLeft : Program Reg :=
  Program.seq (prependRecord write right) <|
  Program.seq (Program.read left cur) <|
  Program.seq (prependRecord cur right) (Program.clear cur)

def motion : Program Reg :=
  Program.branch (UnaryPrograms.isTrue dir)
    (Program.seq (Program.pop dir) (Program.branch (UnaryPrograms.isTrue dir)
      (prependRecord write left) (prependRecord write right))) motionLeft

def shiftTape (x : ℕ) (d : Move) (L R : List ℕ) : List ℕ × List ℕ := match d with
  | .left => (L.tail,L.headD 0::x::R)
  | .stay => (L,x::R)
  | .right => (x::L,R)

def movedDir : Move → ℕ
  | .right => 1 | _ => 0

theorem motionLeft_exec (s : Stacks Reg Bool) (L R : List ℕ) (x : ℕ)
    (hl : s left=fields L) (hr : s right=fields R)
    (hx : s write=numeral x) (hc : s cur=[]) :
    motionLeft.Exec s (12*x+20*L.headD 0+12)
      (Function.update (Function.update s left (fields L.tail)) right (fields (L.headD 0::x::R))) := by
  let a := Function.update s right (fields (x::R))
  let b := Function.update (Function.update a left (fields L.tail)) cur (numeral (L.headD 0))
  let c := Function.update b right (fields (L.headD 0::x::R))
  have h1 : (prependRecord write right).Exec s (12*x+4) a := by
    simpa [a,hr] using prependRecord_exec write right (by decide) x s hx
  have h2 : (Program.read left cur).Exec a (5*L.headD 0+3) b := by
    simpa [b,a,hl,hc] using Program.read_exec left cur (by decide) a
  have h3 : (prependRecord cur right).Exec b (12*L.headD 0+4) c := by
    simpa [c,b,a] using prependRecord_exec cur right (by decide) (L.headD 0) b (by simp [b])
  have h4 := Program.clear_exec cur c
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3 h4))
  have hout : Function.update c cur []=
      Function.update (Function.update s left (fields L.tail)) right (fields (L.headD 0::x::R)) := by
    funext r; cases r <;> simp [c,b,a,hc]
  rw [hout] at he
  convert he using 1 <;> try rfl
  simp [c,b]
  omega

theorem motion_exec (s : Stacks Reg Bool) (L R : List ℕ) (x : ℕ) (d : Move)
    (hl : s left=fields L) (hr : s right=fields R)
    (hx : s write=numeral x) (hc : s cur=[])
    (hd : s dir=numeral (Diagonal.moveCode d)) :
    ∃t≤12*x+20*L.headD 0+17,motion.Exec s t
      (Function.update (Function.update (Function.update s dir (numeral (movedDir d)))
        left (fields (shiftTape x d L R).1)) right (fields (shiftTape x d L R).2)) := by
  cases d with
  | left =>
    have he := Program.branch_false (p:=Program.seq (Program.pop dir) (Program.branch (UnaryPrograms.isTrue dir)
      (prependRecord write left) (prependRecord write right)))
      (test:=UnaryPrograms.isTrue dir) (by simp [UnaryPrograms.isTrue,tops,hd,Diagonal.moveCode,numeral])
      (motionLeft_exec s L R x hl hr hx hc)
    refine ⟨12*x+20*L.headD 0+13,by omega,?_⟩
    convert he using 1
    all_goals try rfl
    funext r; cases r <;> simp [shiftTape,movedDir,hd,Diagonal.moveCode,numeral]
  | stay =>
    let a := Function.update s dir []
    have h1 : (Program.pop dir).Exec s 2 a := by
      simpa [a,hd,Diagonal.moveCode,numeral] using Program.pop_exec dir s
    have h2 := prependRecord_exec write right (by decide) x a (by simp [a,hx])
    have h3 := Program.branch_false (p:=prependRecord write left) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,a]) h2
    have he := Program.branch_true (q:=motionLeft) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,hd,Diagonal.moveCode,numeral]) (Program.seq_exec h1 h3)
    refine ⟨12*x+8,by omega,?_⟩
    convert he using 1
    all_goals try rfl
    all_goals try omega
    funext r; cases r <;> simp [a,shiftTape,movedDir,hl,hr,numeral]
  | right =>
    let a := Function.update s dir (numeral 1)
    have h1 : (Program.pop dir).Exec s 2 a := by
      simpa [a,hd,Diagonal.moveCode,numeral] using Program.pop_exec dir s
    have h2 := prependRecord_exec write left (by decide) x a (by simp [a,hx])
    have h3 := Program.branch_true (q:=prependRecord write right) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,a,numeral]) h2
    have he := Program.branch_true (q:=motionLeft) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,hd,Diagonal.moveCode,numeral]) (Program.seq_exec h1 h3)
    refine ⟨12*x+8,by omega,?_⟩
    convert he using 1
    all_goals try rfl
    all_goals try omega
    funext r; cases r <;> simp [a,shiftTape,movedDir,hl,hr,numeral]

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def haltFlag (q : ℕ) : List Bool := if q=1 then [false] else if q=2 then [true] else []

def flagTest : Program Reg :=
  Program.branch (UnaryPrograms.isTrue temp)
    (Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp)
      (Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp) Program.skip (Program.push halt true)))
      (Program.push halt false))) Program.skip

def flagState : Program Reg :=
  Program.seq (Program.copy state temp) (Program.seq flagTest (Program.clear temp))

theorem flagTest_exec (s : Stacks Reg Bool) (q : ℕ) (ht : s temp=numeral q) (hh : s halt=[]) :
    ∃t≤10,flagTest.Exec s t
      (Function.update (Function.update s temp (numeral (q-2))) halt (haltFlag q)) := by
  cases q with
  | zero =>
    have he := Program.branch_false (p:=Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp)
      (Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp) Program.skip (Program.push halt true)))
      (Program.push halt false))) (test:=UnaryPrograms.isTrue temp)
      (by simp [UnaryPrograms.isTrue,tops,ht,numeral]) (Program.skip_exec s)
    refine ⟨2,by omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [haltFlag,←ht,hh]
  | succ q =>
    let a := Function.update s temp (numeral q)
    have hp : (Program.pop temp).Exec s 2 a := by
      simpa [a,ht,numeral,List.replicate_succ] using Program.pop_exec temp s
    have htop : UnaryPrograms.isTrue temp (tops s)=true := by simp [UnaryPrograms.isTrue,tops,ht,numeral,List.replicate_succ]
    cases q with
    | zero =>
      have he := Program.branch_true (q:=Program.skip) htop (Program.seq_exec hp
        (Program.branch_false (p:=Program.seq (Program.pop temp)
          (Program.branch (UnaryPrograms.isTrue temp) Program.skip (Program.push halt true))) (test:=UnaryPrograms.isTrue temp)
          (by simp [UnaryPrograms.isTrue,tops,a,numeral]) (Program.push_exec halt false a)))
      refine ⟨6,by omega,?_⟩
      convert he using 1 <;> try rfl
      funext r; cases r <;> simp [a,haltFlag,hh]
    | succ q =>
      let b := Function.update s temp (numeral q)
      have hp' : (Program.pop temp).Exec a 2 b := by
        simpa [a,b,numeral,List.replicate_succ] using Program.pop_exec temp a
      have ht' : UnaryPrograms.isTrue temp (tops a)=true := by simp [UnaryPrograms.isTrue,tops,a,numeral,List.replicate_succ]
      cases q with
      | zero =>
        have he := Program.branch_true (q:=Program.skip) htop (Program.seq_exec hp
          (Program.branch_true (q:=Program.push halt false) ht' (Program.seq_exec hp'
            (Program.branch_false (p:=Program.skip) (test:=UnaryPrograms.isTrue temp)
              (by simp [UnaryPrograms.isTrue,tops,b,numeral]) (Program.push_exec halt true b)))))
        refine ⟨9,by omega,?_⟩
        convert he using 1 <;> try rfl
        funext r; cases r <;> simp [b,haltFlag,hh]
      | succ q =>
        have he := Program.branch_true (q:=Program.skip) htop (Program.seq_exec hp
          (Program.branch_true (q:=Program.push halt false) ht' (Program.seq_exec hp'
            (Program.branch_true (q:=Program.push halt true) (test:=UnaryPrograms.isTrue temp)
              (by simp [UnaryPrograms.isTrue,tops,b,numeral,List.replicate_succ]) (Program.skip_exec b)))))
        refine ⟨8,by omega,?_⟩
        convert he using 1 <;> try rfl
        funext r; cases r <;> simp [b,haltFlag,hh]

theorem flagState_exec (s : Stacks Reg Bool) (q : ℕ)
    (hq : s state=numeral q) (ht : s temp=[]) (hh : s halt=[]) :
    ∃t≤15*q+13,flagState.Exec s t (Function.update s halt (haltFlag q)) := by
  let a := Function.update s temp (numeral q)
  have h1 : (Program.copy state temp).Exec s (12*q+2) a := by
    simpa [a,hq,ht] using Program.copy_exec state temp (by decide) s
  obtain ⟨t,htime,h2⟩ := flagTest_exec a q (by simp [a]) (by simp [a,hh])
  have h3 := Program.clear_exec temp (Function.update (Function.update a temp (numeral (q-2))) halt (haltFlag q))
  have he := Program.seq_exec h1 (Program.seq_exec h2 h3)
  have hout : Function.update (Function.update (Function.update a temp (numeral (q-2))) halt (haltFlag q)) temp []=
      Function.update s halt (haltFlag q) := by
    funext r; cases r <;> simp [a,ht]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  simp only [Function.update_of_ne (by decide : temp≠halt),Function.update_self,numeral_length]
  omega

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def zeroSymbol (M : OneTape) : Fin M.symbols := ⟨0,by have := M.symbols_ge; omega⟩

def store (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) (m : ℕ) :
    Stacks Reg Bool
  | .tab => Diagonal.tableBits (Diagonal.raw M).table
  | .alpha => numeral M.symbols
  | .state => numeral q.val
  | .left => fields (T.left.map Fin.val)
  | .right => fields (T.right.map Fin.val)
  | .base => numeral m
  | .halt => haltFlag q.val
  | _ => []

@[simp] theorem map_head_val {n : ℕ} (xs : List (Fin n)) (z : Fin n) (hz : z.val=0) :
    (xs.map Fin.val).headD 0=(xs.headD z).val := by cases xs <;> simp [hz]

@[simp] theorem map_head_zero (M : OneTape) (xs : List (Fin M.symbols)) :
    (xs.map Fin.val).headD 0=(xs.headD (zeroSymbol M)).val :=
  map_head_val xs (zeroSymbol M) rfl

@[simp] theorem table_lookup (M : OneTape) (q : Fin M.states) (x : Fin M.symbols)
    (hi : q.val*M.symbols+x.val<(Diagonal.raw M).table.length) :
    (Diagonal.raw M).table[q.val*M.symbols+x.val]=
      ((M.transition q x).1.val,(M.transition q x).2.1.val,Diagonal.moveCode (M.transition q x).2.2) := by
  have hv : (finProdFinEquiv (q,x)).val=q.val*M.symbols+x.val := by
    change x.val+M.symbols*q.val=q.val*M.symbols+x.val
    ring
  have he : (⟨q.val*M.symbols+x.val,by simpa [Diagonal.raw] using hi⟩ : Fin (M.states*M.symbols))=
      finProdFinEquiv (q,x) := Fin.ext hv.symm
  simp only [Diagonal.raw,List.getElem_ofFn,he,Equiv.symm_apply_apply]

def activeStep : Program Reg :=
  Program.seq (Program.read right cur) <|
  Program.seq lookup <|
  Program.seq (Program.clear cur) <|
  Program.seq motion <|
  Program.seq (Program.clear write) <|
  Program.seq (Program.clear dir) flagState

def step : Program Reg := Program.branch (fun v => (v halt).isNone) activeStep Program.skip

def stepBound (M : OneTape) : ℕ :=
  (M.states*M.symbols+1)*(30*(Diagonal.tableBits (Diagonal.raw M).table).length+
    60*M.states+60*M.symbols+100)+50*M.states+100*M.symbols+100

def nextState (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) :=
  if q.val=1 ∨ q.val=2 then q else (M.transition q (T.right.headD (zeroSymbol M))).1

def nextTape (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) :=
  if q.val=1 ∨ q.val=2 then T else
    TapePair.moveWrite (zeroSymbol M) (M.transition q (T.right.headD (zeroSymbol M))).2.1
      (M.transition q (T.right.headD (zeroSymbol M))).2.2 T

theorem activeStep_exec (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) (m : ℕ)
    (hq1 : q.val≠1) (hq2 : q.val≠2) :
    ∃t<stepBound M,activeStep.Exec (store M q T m) t
      (store M (nextState M q T) (nextTape M q T) m) := by
  let s := store M q T m
  let x := T.right.headD (zeroSymbol M)
  let p := M.transition q x
  let L := T.left.map Fin.val
  let R := T.right.tail.map Fin.val
  let a := Function.update (Function.update s right (fields R)) cur (numeral x.val)
  let b := Function.update (Function.update (Function.update a state (numeral p.1.val))
      write (numeral p.2.1.val)) dir (numeral (Diagonal.moveCode p.2.2))
  let c := Function.update b cur []
  let d := Function.update (Function.update (Function.update c dir (numeral (movedDir p.2.2)))
    left (fields (shiftTape p.2.1.val p.2.2 L R).1)) right (fields (shiftTape p.2.1.val p.2.2 L R).2)
  let e := Function.update d write []
  let f := Function.update e dir []
  have h1 : (Program.read right cur).Exec s (5*x.val+3) a := by
    simpa only [s,store,fields_head,fields_tail,map_head_zero,a,R,x,Function.update_self,
      List.map_tail,List.append_nil] using Program.read_exec right cur (by decide) s
  have hi : q.val*M.symbols+x.val<(Diagonal.raw M).table.length := by
    simp only [Diagonal.raw,List.length_ofFn]
    have hq := q.isLt
    have hx := x.isLt
    nlinarith
  obtain ⟨t2,ht2,h2⟩ := lookup_exec (Diagonal.raw M).table q.val M.symbols x.val hi a
    (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a])
    (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a,s,store])
  rw [table_lookup M q x hi] at h2
  change lookup.Exec a t2 b at h2
  have h3 : (Program.clear cur).Exec b (3*x.val+1) c := by
    simpa [c,b,a] using Program.clear_exec cur b
  obtain ⟨t4,ht4,h4⟩ := motion_exec c L R p.2.1.val p.2.2
    (by simp [c,b,a,s,store,L]) (by simp [c,b,a]) (by simp [c,b]) (by simp [c]) (by simp [c,b])
  change motion.Exec c t4 d at h4
  have h5 : (Program.clear write).Exec d (3*p.2.1.val+1) e := by
    simpa [e,d,c,b] using Program.clear_exec write d
  have h6 : (Program.clear dir).Exec e (3*movedDir p.2.2+1) f := by
    simpa [f,e,d] using Program.clear_exec dir e
  obtain ⟨t7,ht7,h7⟩ := flagState_exec f p.1.val
    (by simp [f,e,d,c,b]) (by simp [f,e,d,c,b,a,s,store])
    (by simp [f,e,d,c,b,a,s,store,haltFlag,hq1,hq2])
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3
    (Program.seq_exec h4 (Program.seq_exec h5 (Program.seq_exec h6 h7)))))
  have htape : ((nextTape M q T).left.map Fin.val,(nextTape M q T).right.map Fin.val)=
      shiftTape p.2.1.val p.2.2 L R := by
    simp only [nextTape,hq1,hq2,false_or,ite_false]
    change ((TapePair.moveWrite (zeroSymbol M) p.2.1 p.2.2 T).left.map Fin.val,
      (TapePair.moveWrite (zeroSymbol M) p.2.1 p.2.2 T).right.map Fin.val)=_
    cases hmv : p.2.2 <;> simp only [TapePair.moveWrite,shiftTape,L,R,List.map_cons,
      List.map_tail,map_head_zero]
  have htL := congrArg Prod.fst htape
  have htR := congrArg Prod.snd htape
  have hout : Function.update f halt (haltFlag p.1.val)=
      store M (nextState M q T) (nextTape M q T) m := by
    funext r
    cases r <;> simp [f,e,d,c,b,a,s,store,nextState,hq1,hq2]
    all_goals first | exact congrArg fields htL.symm | exact congrArg fields htR.symm | simp [p,x]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  have ht2' : t2≤(M.states*M.symbols+1)*(30*(Diagonal.tableBits (Diagonal.raw M).table).length+
      60*M.states+60*M.symbols+100) := by
    apply ht2.trans
    apply Nat.mul_le_mul
    · simp only [Diagonal.raw,List.length_ofFn] at hi
      omega
    · have hq := q.isLt
      have hx := x.isLt
      omega
  have hx := x.isLt
  have hy := p.2.1.isLt
  have hq := p.1.isLt
  have hl : L.headD 0<M.symbols := by
    simpa only [L,map_head_zero] using (T.left.headD (zeroSymbol M)).isLt
  have hd : movedDir p.2.2≤1 := by cases p.2.2 <;> decide
  dsimp only [stepBound]
  omega

theorem step_exec (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) (m : ℕ) :
    ∃t ≤ stepBound M,step.Exec (store M q T m) t
      (store M (nextState M q T) (nextTape M q T) m) := by
  by_cases hh : q.val=1 ∨ q.val=2
  · have hf : (tops (store M q T m) halt).isNone=false := by
      rcases hh with h | h <;> simp [tops,store,haltFlag,h]
    have he := Program.branch_false (p:=activeStep) (test:=fun v => (v halt).isNone) hf (Program.skip_exec (store M q T m))
    refine ⟨2,by simp [stepBound],?_⟩
    simpa only [step,nextState,nextTape,hh,ite_true] using he
  · have hq1 : q.val≠1 := fun h => hh (Or.inl h)
    have hq2 : q.val≠2 := fun h => hh (Or.inr h)
    obtain ⟨t,ht,he⟩ := activeStep_exec M q T m hq1 hq2
    refine ⟨t+1,by omega,?_⟩
    exact Program.branch_true (by simp [tops,store,haltFlag,hq1,hq2]) he

end WLTime.Universal

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} {C : Type uC} [DecidableEq K]

theorem countdown_lift (c : Code K Bool) (f : C → C) (enc : C → Stacks K Bool) (B : ℕ)
    (hc : ∀ x,∃ t≤B,c.Exec (enc x) t (enc (f x))) (n : ℕ) (x : C) :
    ∃ t≤n*(B+3)+1,
      (Code.loop (Code.nonempty (.inl 0))
        (.seq (c.relabel Sum.inr) (.pop (.inl 0))) : Code (Fin 2 ⊕ K) Bool).Exec
        (Sum.elim (extra n) (enc x)) t (Sum.elim (extra 0) (enc (f^[n] x))) := by
  induction n generalizing x with
  | zero =>
    refine ⟨1,by omega,?_⟩
    exact .loop_false (by simp [Code.nonempty,tops,extra,numeral])
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := hc x
    have he' := Code.relabel_inr_exec he (extra (n+1))
    have hb := Code.Exec.seq he' (Code.Exec.pop _ (.inl 0))
    rw [extra_succ_update] at hb
    obtain ⟨v,hv,hr⟩ := ih (f x)
    have hh := Code.Exec.loop_true (p:=Code.nonempty (.inl 0))
      (by simp [Code.nonempty,tops,extra,numeral]) hb hr
    refine ⟨u+2+v+1,?_,?_⟩
    · nlinarith
    · simpa only [Function.iterate_succ_apply] using hh

theorem repeat_lift (base : K) (c : Code K Bool) (f : C → C) (enc : C → Stacks K Bool)
    (B n : ℕ) (hc : ∀ x,∃ t≤B,c.Exec (enc x) t (enc (f x)))
    (x : C) (hb : enc x base=numeral n) :
    ∃ t≤n*(B+15)+3,
      (repeatN base c).Exec (Sum.elim (extra 0) (enc x)) t
        (Sum.elim (extra 0) (enc (f^[n] x))) := by
  have hf := Code.copy_exec (.inr base : Fin 2 ⊕ K) (.inl 0) (.inl 1)
    (by simp) (by simp) (by simp) false (Sum.elim (extra 0) (enc x)) (by simp [extra])
  have he : Function.update (Sum.elim (extra 0) (enc x)) (.inl 0)
      (Sum.elim (extra 0) (enc x) (.inr base)++Sum.elim (extra 0) (enc x) (.inl 0))=
      Sum.elim (extra n) (enc x) := by
    funext i
    cases i with
    | inl j => fin_cases j <;> simp [extra,numeral,hb]
    | inr j => simp
  rw [he] at hf
  obtain ⟨u,hu,hr⟩ := countdown_lift c f enc B hc n x
  refine ⟨_,?_,Code.Exec.seq hf hr⟩
  simp only [Sum.elim_inr,hb,numeral,List.length_replicate]
  nlinarith
end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Program
variable {K : Type uK} {C : Type uC} [DecidableEq K]

theorem repeat_lift (base : K) (p : Program K) (f : C → C) (enc : C → Stacks K Bool)
    (B n : ℕ) (hc : ∀ x,∃ t≤B,p.Exec (enc x) t (enc (f x)))
    (x : C) (hb : enc x base=UnaryPrograms.numeral n) :
    ∃ t≤n*(B+15)+3,(repeatN base p).Exec (enc x) t (enc (f^[n] x)) := by
  obtain ⟨t,ht,he⟩ := UnaryPrograms.repeat_lift (.inr base : Fin p.scratch ⊕ K) p.code f
    (fun x => p.ambient (enc x)) B n hc x hb
  refine ⟨t,ht,?_⟩
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) he
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro l hl
    exact False.elim (hl ((merge 2 p.scratch).symm l) (Equiv.apply_symm_apply _ l))

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

abbrev Config (M : OneTape) := Fin M.states × TapePair.Tape (Fin M.symbols)

def next (M : OneTape) (c : Config M) : Config M := (nextState M c.1 c.2,nextTape M c.1 c.2)

def encode (M : OneTape) (m : ℕ) (c : Config M) : Stacks Reg Bool := store M c.1 c.2 m

def steps : ℕ → Program Reg
  | 0 => step
  | s+1 => Program.repeatN base (steps s)

theorem steps_exec (M : OneTape) (m : ℕ) (hm : 0 < m) (s : ℕ) (c : Config M) :
    ∃ t ≤ (stepBound M+18*s)*m^s,
      (steps s).Exec (encode M m c) t (encode M m ((next M)^[m^s] c)) := by
  induction s generalizing c with
  | zero => simpa only [Nat.mul_zero,Nat.add_zero,pow_zero,Nat.mul_one,Function.iterate_one,steps,encode,next]
      using step_exec M c.1 c.2 m
  | succ s ih =>
    obtain ⟨t,ht,he⟩ := Program.repeat_lift base (steps s) ((next M)^[m^s]) (encode M m)
      ((stepBound M+18*s)*m^s) m ih c rfl
    refine ⟨t,?_,?_⟩
    · have hp : 1 ≤ m^s := Nat.one_le_pow _ _ hm
      apply ht.trans
      rw [pow_succ]
      nlinarith
    · simpa only [steps,pow_succ,Function.iterate_mul] using he

end WLTime.Universal

end OAI
