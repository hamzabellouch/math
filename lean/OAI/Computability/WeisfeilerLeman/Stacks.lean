import OAI.Computability.WeisfeilerLeman.Turing

namespace OAI

universe uS uA

namespace WLTime.StackMachine

inductive Command (K a q : ℕ) where
  | next (state : Fin q)
  | push (stack : Fin K) (letter : Fin a) (state : Fin q)
  | pop (stack : Fin K) (state : Fin q)
  | halt (answer : Bool)

structure Machine where
  count : ℕ
  alphabet : ℕ
  states : ℕ
  count_pos : 0< count
  alphabet_ge : 2 ≤ alphabet
  initial : Fin states
  transition : Fin states → (Fin count → Option (Fin alphabet)) →
    Command count alphabet states

namespace Machine
variable (M : Machine)

structure Config where
  state : Bool ⊕ Fin M.states
  stack : Fin M.count → List (Fin M.alphabet)

 def inputLetter (b : Bool) : Fin M.alphabet := ⟨if b then 1 else 0,by have := M.alphabet_ge; split <;> omega⟩

 def initialConfig (w : List Bool) : M.Config where
  state := .inr M.initial
  stack k := if k.val=0 then w.map M.inputLetter else []

 def perform (C : M.Config) (a : Command M.count M.alphabet M.states) : M.Config := match a with
  | .next q => { C with state := .inr q }
  | .push k x q => { state := .inr q,stack := Function.update C.stack k (x::C.stack k) }
  | .pop k q => { state := .inr q,stack := Function.update C.stack k (C.stack k).tail }
  | .halt b => {C with state := .inl b}

 def step (C : M.Config) : M.Config := match C.state with
  | .inl _ => C
  | .inr q => M.perform C (M.transition q (fun k => (C.stack k).head?))

 def run (w : List Bool) (t : ℕ) : M.Config := M.step^[t] (M.initialConfig w)

 def encodeLetter : Option (Fin M.alphabet) → Fin (M.alphabet+1)
  | none => 0
  | some x => x.succ

 def decodeLetter (x : Fin (M.alphabet+1)) : Option (Fin M.alphabet) :=
   Fin.cases none some x

@[simp] theorem decode_encode (x : Option (Fin M.alphabet)) : M.decodeLetter (M.encodeLetter x)=x := by
  cases x <;> rfl

 def contents (s : List (Fin M.alphabet)) (h z : ℤ) : Fin (M.alphabet+1) :=
  if z<h then 0 else M.encodeLetter s[(z-h).toNat]?

@[simp] theorem contents_empty (h z : ℤ) : M.contents [] h z=0 := by
  simp only [contents,List.getElem?_nil,encodeLetter,ite_self]

@[simp] theorem contents_head (s : List (Fin M.alphabet)) (h : ℤ) :
    M.contents s h h=M.encodeLetter s.head? := by
  simp only [contents,lt_self_iff_false,ite_false,sub_self,Int.toNat_zero]
  exact congrArg M.encodeLetter (List.head?_eq_getElem? (l:=s)).symm

theorem contents_push (s : List (Fin M.alphabet)) (h : ℤ) (x : Fin M.alphabet) :
    M.contents (x::s) (h-1)=Function.update (M.contents s h) (h-1) x.succ := by
  funext z
  by_cases he : z=h-1
  · subst z
    simp only [Function.update_self,contents_head,List.head?_cons,encodeLetter]
  · rw [Function.update_of_ne he]
    by_cases hz : z<h-1
    · have hz' : z<h := by omega
      simp only [contents,ite_eq_left hz,ite_eq_left hz']
    · have hz' : ¬z<h := by omega
      have hi : (z-(h-1)).toNat=(z-h).toNat+1 := by omega
      simp only [contents,ite_eq_right hz,ite_eq_right hz',hi,List.getElem?_cons_succ]

theorem contents_pop (s : List (Fin M.alphabet)) (h : ℤ) :
    M.contents s.tail (h+1)=Function.update (M.contents s h) h 0 := by
  funext z
  by_cases he : z=h
  · subst z
    simp only [Function.update_self,contents,ite_eq_left (show h<h+1 by omega)]
  · rw [Function.update_of_ne he]
    by_cases hz : z<h
    · have hz' : z<h+1 := by omega
      simp only [contents,ite_eq_left hz,ite_eq_left hz']
    · have hz' : ¬z<h+1 := by omega
      have hi : (z-h).toNat=(z-(h+1)).toNat+1 := by omega
      simp only [contents,ite_eq_right hz,ite_eq_right hz',List.getElem?_tail,hi]

abbrev Micro := Fin 3 ⊕ (Fin M.states ⊕ (Fin M.count × Fin M.alphabet × Fin M.states))

noncomputable def microEquiv : M.Micro ≃ Fin (3+Fintype.card (Fin M.states ⊕
    (Fin M.count × Fin M.alphabet × Fin M.states))) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _)).trans finSumFinEquiv

@[simp] theorem micro_left (i : Fin 3) : (M.microEquiv (.inl i)).val=i.val := rfl

 theorem micro_right_ge (v : Fin M.states ⊕ (Fin M.count × Fin M.alphabet × Fin M.states)) :
    3 ≤ (M.microEquiv (.inr v)).val := by
  change 3 ≤ 3+(Fintype.equivFin _ v).val
  omega

 def microTransition (p : M.Micro) (read : Fin M.count → Fin (M.alphabet+1)) :
    M.Micro × (Fin M.count → Fin (M.alphabet+1)) × (Fin M.count → Move) := match p with
  | .inl i => ((if i.val=0 then .inr (.inl M.initial) else .inl i),read,fun _ => .stay)
  | .inr (.inr (k,x,q)) => (.inr (.inl q),Function.update read k x.succ,fun _ => .stay)
  | .inr (.inl q) => match M.transition q (fun k => M.decodeLetter (read k)) with
    | .next q' => (.inr (.inl q'),read,fun _ => .stay)
    | .push k x q' => (.inr (.inr (k,x,q')),read,Function.update (fun _ => .stay) k .left)
    | .pop k q' => (.inr (.inl q'),Function.update read k 0,Function.update (fun _ => .stay) k .right)
    | .halt b => (.inl (if b then 1 else 2),read,fun _ => .stay)

noncomputable abbrev compile : TM where
  tapes := M.count
  states := 3+Fintype.card (Fin M.states ⊕ (Fin M.count × Fin M.alphabet × Fin M.states))
  symbols := M.alphabet+1
  tapes_pos := M.count_pos
  states_ge := by omega
  symbols_ge := by have := M.alphabet_ge; omega
  transition q read := let a := M.microTransition (M.microEquiv.symm q) read
    (M.microEquiv a.1,a.2)

noncomputable def stateCode : Bool ⊕ Fin M.states → Fin M.compile.states
  | .inl b => M.microEquiv (.inl (if b then 1 else 2))
  | .inr q => M.microEquiv (.inr (.inl q))

noncomputable def embed (C : M.Config) (h : Fin M.count → ℤ) : M.compile.Config where
  state := M.stateCode C.state
  head := h
  tape k := M.contents (C.stack k) (h k)

 theorem embed_halted (C : M.Config) (h : Fin M.count → ℤ) :
    M.compile.halted (M.embed C h) ↔ ∃ b,C.state=.inl b := by
  unfold TM.halted embed stateCode
  cases C.state with
  | inl b => cases b <;> simp
  | inr q =>
    have he := M.micro_right_ge (.inl q)
    simp only [reduceCtorEq,exists_false,iff_false]
    omega

 def cost (a : Command M.count M.alphabet M.states) : ℕ := match a with
  | .push _ _ _ => 2
  | _ => 1

 def moveHeads (h : Fin M.count → ℤ) (a : Command M.count M.alphabet M.states) : Fin M.count → ℤ := match a with
  | .push k _ _ => Function.update h k (h k-1)
  | .pop k _ => Function.update h k (h k+1)
  | _ => h

 theorem write_same (tape : Fin M.count → ℤ → Fin (M.alphabet+1)) (h : Fin M.count → ℤ) :
    (fun k z => if z=h k then tape k (h k) else tape k z)=tape := by
  funext k z
  split <;> rename_i he
  · exact congrArg (tape k) he.symm
  · rfl

 theorem write_one (tape : Fin M.count → ℤ → Fin (M.alphabet+1)) (h : Fin M.count → ℤ)
    (k : Fin M.count) (x : Fin (M.alphabet+1)) :
    (fun j z => if z=h j then (Function.update (fun i => tape i (h i)) k x) j else tape j z)=
      Function.update tape k (Function.update (tape k) (h k) x) := by
  funext j z
  by_cases hj : j=k
  · subst j
    simp only [Function.update_self,Function.update_apply]
  · simp only [Function.update_of_ne hj]
    split <;> rename_i he
    · exact congrArg (tape j) he.symm
    · rfl

 theorem step_micro (p : M.Micro) (hp : (M.microEquiv p).val≠1 ∧ (M.microEquiv p).val≠2)
    (h : Fin M.count → ℤ) (tape : Fin M.count → ℤ → Fin (M.alphabet+1)) :
    M.compile.step {state:=M.microEquiv p,head:=h,tape:=tape}=
      let a := M.microTransition p (fun k => tape k (h k))
      {state:=M.microEquiv a.1,head:=fun k => h k+(a.2.2 k).displacement,
       tape:=fun k z => if z=h k then a.2.1 k else tape k z} := by
  have hh : ¬M.compile.halted {state:=M.microEquiv p,head:=h,tape:=tape} := by
    exact fun he => he.elim hp.1 hp.2
  rw [TM.step,ite_eq_right hh]
  simp only [compile,Equiv.symm_apply_apply]

 theorem heads_one (h : Fin M.count → ℤ) (k : Fin M.count) (d : Move) :
    (fun j => h j+(Function.update (fun _ => Move.stay) k d j).displacement)=
      Function.update h k (h k+d.displacement) := by
  funext j
  by_cases hj : j=k
  · subst j; simp
  · simp [Function.update_of_ne hj,Move.displacement]

 theorem tame_right (p : Fin M.states ⊕ (Fin M.count × Fin M.alphabet × Fin M.states)) :
    (M.microEquiv (.inr p)).val≠1 ∧ (M.microEquiv (.inr p)).val≠2 := by
  have := M.micro_right_ge p
  omega

 theorem simulate_action (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (h : Fin M.count → ℤ) (a : Command M.count M.alphabet M.states)
    (ha : M.transition q (fun k => (s k).head?)=a) :
    M.compile.step^[M.cost a] (M.embed ⟨.inr q,s⟩ h)=
      M.embed (M.perform ⟨.inr q,s⟩ a) (M.moveHeads h a) := by
  have read_eq : (fun k => M.decodeLetter (M.contents (s k) (h k) (h k)))=
      (fun k => (s k).head?) := by
    funext k
    rw [M.contents_head,M.decode_encode]
  cases a with
  | next q' =>
    change M.compile.step (M.embed ⟨.inr q,s⟩ h)=_
    rw [embed,stateCode,M.step_micro _ (M.tame_right _) h]
    simp only [microTransition,read_eq,ha,Move.displacement,add_zero,M.write_same,
      perform,moveHeads,embed,stateCode]
  | halt b =>
    change M.compile.step (M.embed ⟨.inr q,s⟩ h)=_
    rw [embed,stateCode,M.step_micro _ (M.tame_right _) h]
    simp only [microTransition,read_eq,ha,Move.displacement,add_zero,M.write_same,
      perform,moveHeads,embed,stateCode]
  | pop k q' =>
    change M.compile.step (M.embed ⟨.inr q,s⟩ h)=_
    rw [embed,stateCode,M.step_micro _ (M.tame_right _) h]
    simp only [microTransition,read_eq,ha,Move.displacement,M.write_one,
      perform,moveHeads,embed,stateCode]
    congr 1
    · funext j
      by_cases hj : j=k <;> simp [hj]
    · funext j
      by_cases hj : j=k
      · subst j
        simp only [Function.update_self,M.contents_pop]
      · simp only [Function.update_of_ne hj]
  | push k x q' =>
    change M.compile.step (M.compile.step (M.embed ⟨.inr q,s⟩ h))=_
    rw [embed,stateCode,M.step_micro _ (M.tame_right _) h]
    simp only [microTransition,read_eq,ha,Move.displacement,M.write_same]
    rw [M.step_micro _ (M.tame_right _)]
    simp only [microTransition,Move.displacement,add_zero,M.write_one,
      perform,moveHeads,embed,stateCode]
    congr 1
    · funext j
      by_cases hj : j=k <;> simp [hj]
      all_goals omega
    · funext j
      by_cases hj : j=k
      · subst j
        simp only [Function.update_self]
        rw [show h k + (-1)=h k-1 by omega,← M.contents_push]
      · simp only [Function.update_of_ne hj]

theorem initial_tape (w : List Bool) : (M.compile.initial w).tape=
    (fun k => M.contents ((M.initialConfig w).stack k) 0) := by
  funext k z
  by_cases hk : k.val=0
  · simp only [TM.initial,initialConfig,hk,ite_true,true_and,contents]
    by_cases hz : z<0
    · have hz' : ¬0 ≤ z := by omega
      simp only [ite_eq_left hz,hz',false_and,ite_false]
      rfl
    · have hz' : 0 ≤ z := by omega
      simp only [ite_eq_right hz,hz',true_and,sub_zero,List.getElem?_map]
      by_cases hi : z.toNat<w.length
      · rw [ite_eq_left hi,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
        cases w[z.toNat] <;> rfl
      · rw [ite_eq_right hi,List.getElem?_eq_none (by omega)]
        rfl
  · simp only [TM.initial,initialConfig,hk,false_and,ite_false,M.contents_empty]
    rfl

theorem initial_step (w : List Bool) :
    M.compile.run w 1=M.embed (M.initialConfig w) (fun _ => 0) := by
  have hi : M.compile.initial w =
      { state := M.microEquiv (.inl 0)
        head := fun _ => 0
        tape := fun k => M.contents ((M.initialConfig w).stack k) 0 } := by
    rw [← M.initial_tape w]
    rfl
  change M.compile.step (M.compile.initial w)=_
  rw [hi,M.step_micro _ (by simp) _]
  simp only [microTransition,Fin.val_zero,ite_true,Move.displacement,add_zero,
    M.write_same,embed,stateCode,initialConfig]

theorem simulate_step (C : M.Config) (h : Fin M.count → ℤ) :
    ∃ t ≤ 2, ∃ h',M.compile.step^[t] (M.embed C h)=M.embed (M.step C) h' := by
  rcases C with ⟨b|q,s⟩
  · exact ⟨0,by omega,h,rfl⟩
  · let a := M.transition q (fun k => (s k).head?)
    refine ⟨M.cost a,?_,M.moveHeads h a,M.simulate_action s q h a rfl⟩
    cases a <;> simp [cost]

theorem simulate_iterate (C : M.Config) (h : Fin M.count → ℤ) (t : ℕ) :
    ∃ u ≤ 2*t, ∃ h',M.compile.step^[u] (M.embed C h)=M.embed (M.step^[t] C) h' := by
  induction t with
  | zero => exact ⟨0,by omega,h,rfl⟩
  | succ t ih =>
    obtain ⟨u,hu,h',he⟩ := ih
    obtain ⟨v,hv,h'',hf⟩ := M.simulate_step (M.step^[t] C) h'
    refine ⟨v+u,by omega,h'',?_⟩
    rw [Function.iterate_add_apply,he,hf,Function.iterate_succ_apply']

theorem simulate_run (w : List Bool) (t : ℕ) :
    ∃ u ≤ 2*t+1, ∃ h,M.compile.run w u=M.embed (M.run w t) h := by
  obtain ⟨u,hu,h,he⟩ := M.simulate_iterate (M.initialConfig w) (fun _ => 0) t
  refine ⟨u+1,by omega,h,?_⟩
  rw [TM.run_add,M.initial_step,he]
  rfl

theorem compile_correct (w : List Bool) (t : ℕ) (b : Bool)
    (hh : (M.run w t).state=.inl b) :
    M.compile.halts w ∧ M.compile.time w ≤ 2*t+1 ∧ (M.compile.accepts w ↔ b=true) := by
  obtain ⟨u,hu,h,he⟩ := M.simulate_run w t
  have hx : M.compile.halted (M.compile.run w u) := by
    rw [he,M.embed_halted]
    exact ⟨b,hh⟩
  refine ⟨⟨u,hx⟩,(M.compile.time_le_of_halted w hx).trans hu,?_⟩
  rw [M.compile.accepts_iff_at_halt w hx,he]
  simp only [embed,stateCode,hh]
  cases b <;> simp

end Machine
end WLTime.StackMachine

namespace WLTime.TypedTape

abbrev State (S : Type uS) := Fin 3 ⊕ S
abbrev Symbol (A : Type uA) := Fin 3 ⊕ A

structure Machine (S : Type uS) (A : Type uA) where
  transition : State S → Symbol A → State S × Symbol A × Move

structure Config (S : Type uS) (A : Type uA) where
  state : State S
  head : ℤ
  tape : ℤ → Symbol A

namespace Machine
variable {S : Type uS} {A : Type uA} (M : Machine S A)

 def halted (_M : Machine S A) (p : State S) : Prop := p = .inl 1 ∨ p = .inl 2

instance (p : State S) : Decidable (M.halted p) := by
  cases p with
  | inl i => exact decidable_of_iff (i=1 ∨ i=2) (by simp [halted])
  | inr q => exact isFalse (by simp [halted])

 def action (p : State S) (x : Symbol A) : State S × Symbol A × Move :=
  if M.halted p then (p,x,.stay) else M.transition p x

 def step (C : Config S A) : Config S A :=
  let a := M.action C.state (C.tape C.head)
  { state := a.1
    head := C.head+a.2.2.displacement
    tape := Function.update C.tape C.head a.2.1 }

 def initial (_M : Machine S A) (w : List Bool) : Config S A where
  state := .inl 0
  head := 0
  tape z := if 0 ≤ z ∧ z.toNat<w.length then
    .inl (if w.getD z.toNat false then 2 else 1) else .inl 0

 def run (w : List Bool) (t : ℕ) := M.step^[t] (M.initial w)

theorem step_live (p : S) (z : ℤ) (tape : ℤ → Symbol A)
    (q : State S) (x : Symbol A) (d : Move)
    (h : M.transition (.inr p) (tape z)=(q,x,d)) :
    M.step ⟨.inr p,z,tape⟩=⟨q,z+d.displacement,Function.update tape z x⟩ := by
  simp only [step,action,halted,reduceCtorEq,or_self,ite_false,h]

theorem step_keep (p : S) (z : ℤ) (tape : ℤ → Symbol A)
    (q : State S) (d : Move)
    (h : M.transition (.inr p) (tape z)=(q,tape z,d)) :
    M.step ⟨.inr p,z,tape⟩=⟨q,z+d.displacement,tape⟩ := by
  rw [M.step_live p z tape q (tape z) d h]
  congr 1
  exact Function.update_eq_self _ _

theorem path_iterate (C : ℕ → Config S A) (n : ℕ)
    (h : ∀ i<n,M.step (C i)=C (i+1)) : M.step^[n] (C 0)=C n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih (fun i hi => h i (by omega))]
    exact h n (by omega)

theorem concat {C D E : Config S A} {a b : ℕ}
    (h : M.step^[a] C=D) (g : M.step^[b] D=E) : M.step^[a+b] C=E := by
  rw [Nat.add_comm,Function.iterate_add_apply,h,g]

variable [Fintype S] [Fintype A]

noncomputable def stateEquiv (_M : Machine S A) : State S ≃ Fin (3+Fintype.card S) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin S)).trans finSumFinEquiv

noncomputable def symbolEquiv (_M : Machine S A) : Symbol A ≃ Fin (3+Fintype.card A) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin A)).trans finSumFinEquiv

omit [Fintype A] in
@[simp] theorem state_left (i : Fin 3) : (M.stateEquiv (.inl i)).val=i.val := rfl
omit [Fintype S] in
@[simp] theorem symbol_left (i : Fin 3) : (M.symbolEquiv (.inl i)).val=i.val := rfl

omit [Fintype A] in
theorem state_halted (p : State S) :
    ((M.stateEquiv p).val=1 ∨ (M.stateEquiv p).val=2) ↔ M.halted p := by
  cases p with
  | inl i => simp [halted,Fin.ext_iff]
  | inr q =>
    have h : 3 ≤ (M.stateEquiv (.inr q)).val := by
      change 3 ≤ 3+(Fintype.equivFin S q).val
      omega
    simp only [halted,reduceCtorEq,or_self,iff_false]
    omega

noncomputable abbrev compile : OneTape where
  states := 3+Fintype.card S
  symbols := 3+Fintype.card A
  states_ge := by omega
  symbols_ge := by omega
  transition p x := let a := M.transition (M.stateEquiv.symm p) (M.symbolEquiv.symm x)
    (M.stateEquiv a.1,M.symbolEquiv a.2.1,a.2.2)

noncomputable def embed (C : Config S A) : M.compile.Config ℤ where
  state := M.stateEquiv C.state
  head := C.head
  tape z := M.symbolEquiv (C.tape z)

theorem compile_action (p : State S) (x : Symbol A) :
    M.compile.action (M.stateEquiv p) (M.symbolEquiv x) =
      (M.stateEquiv (M.action p x).1,M.symbolEquiv (M.action p x).2.1,(M.action p x).2.2) := by
  simp only [OneTape.action,M.state_halted,action]
  split_ifs <;> simp

theorem embed_step (C : Config S A) :
    M.embed (M.step C)=M.compile.step OneTape.lineShift (M.embed C) := by
  simp only [embed,step,OneTape.step,M.compile_action,OneTape.moveAt_line]
  congr 1
  funext z
  simp only [Function.update_apply]
  split <;> rfl

theorem embed_initial (w : List Bool) : M.embed (M.initial w)=M.compile.initial w := by
  unfold embed initial OneTape.initial
  congr 1
  funext z
  dsimp only
  by_cases h : 0 ≤ z ∧ z.toNat<w.length
  · simp [h,TM.symbol]
    split_ifs <;> rfl
  · simp [h]
    rfl

theorem embed_run (w : List Bool) (t : ℕ) :
    M.embed (M.run w t)=M.compile.run OneTape.lineShift (M.compile.initial w) t := by
  induction t with
  | zero => exact M.embed_initial w
  | succ t ih =>
    simp only [run,Function.iterate_succ_apply',OneTape.run] at *
    rw [M.embed_step,ih]

end Machine
end WLTime.TypedTape

end OAI
