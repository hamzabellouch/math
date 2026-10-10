import OAI.Computability.WeisfeilerLeman.TapeCompiler

namespace OAI

universe uK uA uS uT

namespace WLTime.TypedStack

inductive Command (K : Type uK) (A : Type uA) (S : Type uS) where
  | next (q : S)
  | push (k : K) (x : A) (q : S)
  | pop (k : K) (q : S)
  | halt (b : Bool)

structure Machine (K : Type uK) (A : Type uA) (S : Type uS) where
  inputStack : K
  inputLetter : Bool → A
  initial : S
  transition : S → (K → Option A) → Command K A S

structure Config (K : Type uK) (A : Type uA) (S : Type uS) where
  state : Bool ⊕ S
  stack : K → List A

namespace Machine
variable {K : Type uK} {A : Type uA} {S : Type uS} [DecidableEq K] (M : Machine K A S)

 def perform (_M : Machine K A S) (C : Config K A S) (a : Command K A S) : Config K A S := match a with
  | .next q => { C with state := .inr q }
  | .push k x q => ⟨.inr q,Function.update C.stack k (x::C.stack k)⟩
  | .pop k q => ⟨.inr q,Function.update C.stack k (C.stack k).tail⟩
  | .halt b => { C with state := .inl b }
 def step (C : Config K A S) : Config K A S := match C.state with
  | .inl _ => C
  | .inr q => M.perform C (M.transition q (fun k => (C.stack k).head?))
 def initialConfig (w : List Bool) : Config K A S :=
  ⟨.inr M.initial,fun k => if k=M.inputStack then w.map M.inputLetter else []⟩
 def run (w : List Bool) (t : ℕ) := M.step^[t] (M.initialConfig w)

variable [Fintype K] [Fintype A] [Fintype S]

noncomputable def registerEquiv : K ≃ Fin (Fintype.card K) :=
  (Equiv.swap M.inputStack ((Fintype.equivFin K).symm ⟨0,Fintype.card_pos_iff.mpr ⟨M.inputStack⟩⟩)).trans
    (Fintype.equivFin K)
omit [Fintype A] [Fintype S] in
@[simp] theorem register_input : (M.registerEquiv M.inputStack).val=0 := by
  simp [registerEquiv]

noncomputable def decodeSymbol (x : Fin (2+Fintype.card A)) : A :=
  match finSumFinEquiv.symm x with
  | .inl b => M.inputLetter (b.val=1)
  | .inr a => (Fintype.equivFin A).symm a

noncomputable def encodeSymbol (_M : Machine K A S) (x : A) : Fin (2+Fintype.card A) :=
  finSumFinEquiv (.inr (Fintype.equivFin A x))

omit [Fintype K] [Fintype S] [DecidableEq K] in
@[simp] theorem decode_encode (x : A) : M.decodeSymbol (M.encodeSymbol x)=x := by
  simp [decodeSymbol,encodeSymbol]

noncomputable def encodeCommand : Command K A S →
    StackMachine.Command (Fintype.card K) (2+Fintype.card A) (Fintype.card S)
  | .next q => .next (Fintype.equivFin S q)
  | .push k x q => .push (M.registerEquiv k) (M.encodeSymbol x) (Fintype.equivFin S q)
  | .pop k q => .pop (M.registerEquiv k) (Fintype.equivFin S q)
  | .halt b => .halt b

noncomputable abbrev compile : StackMachine.Machine where
  count := Fintype.card K
  alphabet := 2+Fintype.card A
  states := Fintype.card S
  count_pos := Fintype.card_pos_iff.mpr ⟨M.inputStack⟩
  alphabet_ge := by omega
  initial := Fintype.equivFin S M.initial
  transition q v := M.encodeCommand
    (M.transition ((Fintype.equivFin S).symm q) (fun k => (v (M.registerEquiv k)).map M.decodeSymbol))

noncomputable def project (C : M.compile.Config) : Config K A S where
  state := C.state.map id (Fintype.equivFin S).symm
  stack k := (C.stack (M.registerEquiv k)).map M.decodeSymbol

 theorem project_perform (C : M.compile.Config) (a : Command K A S) :
    M.project (M.compile.perform C (M.encodeCommand a))=M.perform (M.project C) a := by
  cases a with
  | next q => simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
  | halt b => rfl
  | push k x q =>
    simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
    congr 1
    funext j
    by_cases hj : j=k
    · subst j
      simp only [Function.update_self,List.map_cons,M.decode_encode]
    · have hn : M.registerEquiv j≠M.registerEquiv k := fun hh => hj (M.registerEquiv.injective hh)
      simp only [Function.update_of_ne hj,Function.update_of_ne hn]
  | pop k q =>
    simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
    congr 1
    funext j
    by_cases hj : j=k
    · subst j
      simp only [Function.update_self,List.map_tail]
    · have hn : M.registerEquiv j≠M.registerEquiv k := fun hh => hj (M.registerEquiv.injective hh)
      simp only [Function.update_of_ne hj,Function.update_of_ne hn]

 theorem project_step (C : M.compile.Config) : M.project (M.compile.step C)=M.step (M.project C) := by
  obtain ⟨p,s⟩ := C
  cases p with
  | inl b => rfl
  | inr q =>
    change M.project (M.compile.perform _ (M.encodeCommand _))=_
    rw [M.project_perform]
    simp only [step,project,Sum.map_inr,List.head?_map]

 theorem project_initial (w : List Bool) : M.project (M.compile.initialConfig w)=M.initialConfig w := by
  have hi (b : Bool) : M.decodeSymbol (M.compile.inputLetter b)=M.inputLetter b := by
    cases b <;> rfl
  simp only [project,StackMachine.Machine.initialConfig,Sum.map_inr,Equiv.symm_apply_apply,initialConfig]
  congr 1
  funext k
  have hk : (M.registerEquiv k).val=0 ↔ k=M.inputStack := by
    rw [← M.register_input]
    exact Fin.ext_iff.symm.trans (M.registerEquiv.injective.eq_iff)
  simp only [hk]
  split_ifs
  · simp only [List.map_map]
    exact List.map_congr_left (fun b _ => hi b)
  · rfl

 theorem project_run (w : List Bool) (t : ℕ) : M.project (M.compile.run w t)=M.run w t := by
  induction t with
  | zero => exact M.project_initial w
  | succ t ih =>
    simp only [run,StackMachine.Machine.run,Function.iterate_succ_apply'] at *
    rw [M.project_step,ih]

 theorem compile_halt (w : List Bool) (t : ℕ) (b : Bool)
    (h : (M.run w t).state=.inl b) : (M.compile.run w t).state=.inl b := by
  rw [← M.project_run] at h
  cases he : (M.compile.run w t).state with
  | inl b' => simpa only [project,he,Sum.map_inl,id_eq,Sum.inl.injEq] using h
  | inr q => simp only [project,he,Sum.map_inr,reduceCtorEq] at h

 theorem oneTape_correct (w : List Bool) (t : ℕ) (b : Bool)
    (h : (M.run w t).state=.inl b) :
    M.compile.oneTape.toTM.halts w ∧
      M.compile.oneTape.toTM.time w ≤ 8*(Fintype.card K+1)*(w.length+t+1)^2 ∧
      (M.compile.oneTape.toTM.accepts w ↔ b=true) :=
  M.compile.oneTape_correct w t b (M.compile_halt w t b h)

end Machine
end WLTime.TypedStack

namespace WLTime.TypedStack
namespace Command
variable {K : Type uK} {A : Type uA} {S : Type uS} {T : Type uT}
 def rename (f : S → T) : Command K A S → Command K A T
  | .next q => .next (f q)
  | .push k x q => .push k x (f q)
  | .pop k q => .pop k (f q)
  | .halt b => .halt b
 def redirect (f : S → T) (r : T) : Command K A S → Command K A T
  | .next q => .next (f q)
  | .push k x q => .push k x (f q)
  | .pop k q => .pop k (f q)
  | .halt _ => .next r
end Command

variable {K : Type uK} {A : Type uA} {S : Type uS} {T : Type uT} [DecidableEq K]
abbrev Stacks (K : Type uK) (A : Type uA) := K → List A
abbrev Tops (K : Type uK) (A : Type uA) := K → Option A
 def tops (s : Stacks K A) : Tops K A := fun k => (s k).head?

inductive Execution (tr : S → Tops K A → Command K A S) :
    S → Stacks K A → ℕ → Bool → Stacks K A → Prop
  | halt {q s b} (h : tr q (tops s)=.halt b) : Execution tr q s 1 b s
  | next {q s q' t b out} (h : tr q (tops s)=.next q')
      (tail : Execution tr q' s t b out) : Execution tr q s (t+1) b out
  | push {q s k x q' t b out} (h : tr q (tops s)=.push k x q')
      (tail : Execution tr q' (Function.update s k (x::s k)) t b out) :
      Execution tr q s (t+1) b out
  | pop {q s k q' t b out} (h : tr q (tops s)=.pop k q')
      (tail : Execution tr q' (Function.update s k (s k).tail) t b out) :
      Execution tr q s (t+1) b out

namespace Execution
 theorem iterate (M : Machine K A S) {q s t b out} (h : Execution M.transition q s t b out) :
    M.step^[t] ⟨.inr q,s⟩=⟨.inl b,out⟩ := by
  induction h with
  | @halt q s b h =>
    change M.perform ⟨.inr q,s⟩ (M.transition q (tops s))=⟨.inl b,s⟩
    rw [h]
    rfl
  | @next q s q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih
  | @push q s k x q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih
  | @pop q s k q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih

 theorem rename {tr : S → Tops K A → Command K A S} {tr' : T → Tops K A → Command K A T}
    (f : S → T) (hf : ∀ q v,tr' (f q) v=Command.rename f (tr q v))
    {q s t b out} (h : Execution tr q s t b out) : Execution tr' (f q) s t b out := by
  induction h with
  | halt h => exact .halt (by rw [hf,h]; rfl)
  | next h tail ih => exact .next (by rw [hf,h]; rfl) ih
  | push h tail ih => exact .push (by rw [hf,h]; rfl) ih
  | pop h tail ih => exact .pop (by rw [hf,h]; rfl) ih

 theorem plug {tr : S → Tops K A → Command K A S} {tr' : T → Tops K A → Command K A T}
    (f : S → T) (r : T) (hf : ∀ q v,tr' (f q) v=Command.redirect f r (tr q v))
    {q s t b mid} (h : Execution tr q s t b mid)
    {u c out} (cont : Execution tr' r mid u c out) : Execution tr' (f q) s (t+u) c out := by
  induction h with
  | halt h =>
    simpa only [Nat.add_comm] using Execution.next (by rw [hf,h]; rfl) cont
  | next h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.next (by rw [hf,h]; rfl) (ih cont)
  | push h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.push (by rw [hf,h]; rfl) (ih cont)
  | pop h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.pop (by rw [hf,h]; rfl) (ih cont)
end Execution

inductive Code (K : Type uK) (A : Type uA) where
  | skip
  | push (k : K) (x : A)
  | pushDyn (k : K) (letter : Tops K A → A)
  | pop (k : K)
  | seq (left right : Code K A)
  | branch (test : Tops K A → Bool) (yes no : Code K A)
  | loop (test : Tops K A → Bool) (body : Code K A)

namespace Code
 @[reducible] def State : Code K A → Type
  | .skip => Unit
  | .push _ _ => Fin 2
  | .pushDyn _ _ => Fin 2
  | .pop _ => Fin 2
  | .seq a b => a.State ⊕ b.State
  | .branch _ a b => Unit ⊕ (a.State ⊕ b.State)
  | .loop _ a => Unit ⊕ a.State

noncomputable instance stateFintype (c : Code K A) : Fintype c.State := by
  induction c with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push k x => exact inferInstanceAs (Fintype (Fin 2))
  | pushDyn k f => exact inferInstanceAs (Fintype (Fin 2))
  | pop k => exact inferInstanceAs (Fintype (Fin 2))
  | seq a b ha hb => exact inferInstanceAs (Fintype (a.State ⊕ b.State))
  | branch p a b ha hb => exact inferInstanceAs (Fintype (Unit ⊕ (a.State ⊕ b.State)))
  | loop p a ha => exact inferInstanceAs (Fintype (Unit ⊕ a.State))

 def entry : (c : Code K A) → c.State
  | .skip => ()
  | .push _ _ => 0
  | .pushDyn _ _ => 0
  | .pop _ => 0
  | .seq a _ => .inl a.entry
  | .branch _ _ _ => .inl ()
  | .loop _ _ => .inl ()

 def transition : (c : Code K A) → c.State → Tops K A → Command K A c.State
  | .skip,_,_ => .halt false
  | .push k x,q,_ => if q=0 then .push k x 1 else .halt false
  | .pushDyn k f,q,v => if q=0 then .push k (f v) 1 else .halt false
  | .pop k,q,_ => if q=0 then .pop k 1 else .halt false
  | .seq a b,.inl q,v => Command.redirect Sum.inl (.inr b.entry) (a.transition q v)
  | .seq _ b,.inr q,v => Command.rename Sum.inr (b.transition q v)
  | .branch p a b,.inl _,v => .next (if p v then .inr (.inl a.entry) else .inr (.inr b.entry))
  | .branch _ a _,.inr (.inl q),v => Command.rename (Sum.inr ∘ Sum.inl) (a.transition q v)
  | .branch _ _ b,.inr (.inr q),v => Command.rename (Sum.inr ∘ Sum.inr) (b.transition q v)
  | .loop p a,.inl _,v => if p v then .next (.inr a.entry) else .halt false
  | .loop _ a,.inr q,v => Command.redirect Sum.inr (.inl ()) (a.transition q v)

 def machine (c : Code K A) (k : K) (bits : Bool → A) : Machine K A c.State :=
  ⟨k,bits,c.entry,c.transition⟩

inductive Exec : Code K A → Stacks K A → ℕ → Stacks K A → Prop
  | skip (s) : Exec .skip s 1 s
  | push (s k x) : Exec (.push k x) s 2 (Function.update s k (x::s k))
  | pushDyn (s k f) : Exec (.pushDyn k f) s 2 (Function.update s k (f (tops s)::s k))
  | pop (s k) : Exec (.pop k) s 2 (Function.update s k (s k).tail)
  | seq {a b s mid out t u} (first : Exec a s t mid) (second : Exec b mid u out) :
      Exec (.seq a b) s (t+u) out
  | branch_true {p a b s t out} (test : p (tops s)=true) (body : Exec a s t out) :
      Exec (.branch p a b) s (t+1) out
  | branch_false {p a b s t out} (test : p (tops s)=false) (body : Exec b s t out) :
      Exec (.branch p a b) s (t+1) out
  | loop_false {p a s} (test : p (tops s)=false) : Exec (.loop p a) s 1 s
  | loop_true {p a s mid out t u} (test : p (tops s)=true)
      (body : Exec a s t mid) (rest : Exec (.loop p a) mid u out) :
      Exec (.loop p a) s (t+u+1) out

 theorem exec_finite {c : Code K A} {s t out} (h : c.Exec s t out) :
    Execution c.transition c.entry s t false out := by
  induction h with
  | skip s => exact .halt rfl
  | push s k x =>
    exact .push (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | pushDyn s k f =>
    exact .push (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | pop s k =>
    exact .pop (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | @seq a b s mid out t u first second ih1 ih2 =>
    exact ih1.plug Sum.inl (.inr b.entry) (fun _ _ => rfl) (ih2.rename Sum.inr (fun _ _ => rfl))
  | branch_true hp body ih =>
    exact .next (by simp [entry,transition,hp]) (ih.rename (Sum.inr ∘ Sum.inl) (fun _ _ => rfl))
  | branch_false hp body ih =>
    exact .next (by simp [entry,transition,hp]) (ih.rename (Sum.inr ∘ Sum.inr) (fun _ _ => rfl))
  | loop_false hp => exact .halt (by simp [entry,transition,hp])
  | loop_true hp body rest ih1 ih2 =>
    exact .next (by simp [entry,transition,hp])
      (ih1.plug Sum.inr (.inl ()) (fun _ _ => rfl) ih2)

 theorem exec_iterate (c : Code K A) (k : K) (bits : Bool → A) {s t out} (h : c.Exec s t out) :
    (c.machine k bits).step^[t] ⟨.inr c.entry,s⟩=⟨.inl false,out⟩ :=
  (exec_finite h).iterate (c.machine k bits)

end Code
end WLTime.TypedStack

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

 def nonempty (k : K) (v : Tops K A) : Bool := (v k).isSome
 def clear (k : K) : Code K A := .loop (nonempty k) (.pop k)
 def transfer (a b : K) (zero : A) : Code K A :=
  .loop (nonempty a) (.seq (.pushDyn b (fun v => (v a).getD zero)) (.pop a))

 theorem clear_exec (k : K) (s : Stacks K A) :
    (clear k).Exec s (3*(s k).length+1) (Function.update s k []) := by
  generalize hx : s k=xs
  induction xs generalizing s with
  | nil =>
    have hs : Function.update s k []=s := by rw [← hx]; exact Function.update_eq_self k s
    rw [hs]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    have hstep := ih (Function.update s k xs) (by simp)
    have he : (Function.update (Function.update s k xs) k [])=Function.update s k [] := by simp
    rw [he] at hstep
    have first : Exec (.pop k) s 2 (Function.update s k xs) := by
      simpa only [hx,List.tail_cons] using Exec.pop s k
    have hh := Exec.loop_true (p:=nonempty k) (by simp [nonempty,tops,hx]) first hstep
    convert hh using 1 <;> simp [clear]
    omega

 theorem transfer_exec (a b : K) (hab : a≠b) (zero : A) (s : Stacks K A) :
    (transfer a b zero).Exec s (5*(s a).length+1)
      (Function.update (Function.update s a []) b ((s a).reverse++s b)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update s a []) b (([] : List A).reverse++s b)=s := by
      simp only [List.reverse_nil,List.nil_append]
      rw [← hx,Function.update_eq_self]
      exact Function.update_eq_self b s
    rw [hout]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    let s₁ := Function.update s b (x::s b)
    let s₂ := Function.update s₁ a xs
    have hs₁a : s₁ a=x::xs := by simp [s₁,Function.update_of_ne hab,hx]
    have hs₂a : s₂ a=xs := by simp [s₂]
    have body : Exec (.seq (.pushDyn b (fun v => (v a).getD zero)) (.pop a)) s 4 s₂ := by
      have hp : Exec (.pushDyn b (fun v => (v a).getD zero)) s 2 s₁ := by
        simpa [tops,hx,s₁] using Exec.pushDyn s b (fun v => (v a).getD zero)
      have hq : Exec (.pop a) s₁ 2 s₂ := by
        simpa [hs₁a,s₂] using Exec.pop s₁ a
      exact .seq hp hq
    have hrest := ih s₂ hs₂a
    have hout : Function.update (Function.update s₂ a []) b (xs.reverse++s₂ b)=
        Function.update (Function.update s a []) b ((x::xs).reverse++s b) := by
      funext k
      by_cases hb : k=b
      · subst k
        simp [s₂,s₁,hab.symm,List.reverse_cons,List.append_assoc]
      · by_cases ha : k=a
        · subst k
          simp [hb]
        · simp [s₂,s₁,hb,ha]
    rw [hout] at hrest
    have hh := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hx]) body hrest
    convert hh using 1 <;> simp [transfer]
    omega

 def distribute (a b c : K) (zero : A) : Code K A :=
  .loop (nonempty a) (.seq (.pushDyn b (fun v => (v a).getD zero))
    (.seq (.pushDyn c (fun v => (v a).getD zero)) (.pop a)))

 theorem distribute_exec (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (zero : A) (s : Stacks K A) :
    (distribute a b c zero).Exec s (7*(s a).length+1)
      (Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
        c ((s a).reverse++s c)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update (Function.update s a []) b ([]++s b)) c ([]++s c)=s := by
      simp only [List.nil_append]
      rw [← hx,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    change Exec _ s 1 (Function.update (Function.update (Function.update s a []) b ([]++s b)) c ([]++s c))
    rw [hout]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    let s₁ := Function.update s b (x::s b)
    let s₂ := Function.update s₁ c (x::s c)
    let s₃ := Function.update s₂ a xs
    have hs₁a : s₁ a=x::xs := by simp [s₁,hab,hx]
    have hs₁c : s₁ c=s c := by simp [s₁,hbc.symm]
    have hs₂a : s₂ a=x::xs := by simp [s₂,hac,hs₁a]
    have hs₃a : s₃ a=xs := by simp [s₃]
    have first : Exec (.pushDyn b (fun v => (v a).getD zero)) s 2 s₁ := by
      simpa [tops,hx,s₁] using Exec.pushDyn s b (fun v => (v a).getD zero)
    have second : Exec (.pushDyn c (fun v => (v a).getD zero)) s₁ 2 s₂ := by
      simpa [tops,hs₁a,hs₁c,s₂] using Exec.pushDyn s₁ c (fun v => (v a).getD zero)
    have third : Exec (.pop a) s₂ 2 s₃ := by
      simpa [hs₂a,s₃] using Exec.pop s₂ a
    have body := Exec.seq first (Exec.seq second third)
    have hrest := ih s₃ hs₃a
    have hout : Function.update (Function.update (Function.update s₃ a []) b (xs.reverse++s₃ b))
        c (xs.reverse++s₃ c)=Function.update (Function.update (Function.update s a [])
          b ((x::xs).reverse++s b)) c ((x::xs).reverse++s c) := by
      funext k
      by_cases hc : k=c
      · subst k
        simp [s₃,s₂,s₁,hac.symm,List.reverse_cons,List.append_assoc]
      · by_cases hb : k=b
        · subst k
          simp [s₃,s₂,s₁,hab.symm,hbc,List.reverse_cons,List.append_assoc]
        · by_cases ha : k=a
          · subst k
            simp [hc,hb]
          · simp [s₃,s₂,s₁,hc,hb,ha]
    rw [hout] at hrest
    have hh := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hx]) body hrest
    convert hh using 1 <;> simp [distribute]
    omega

end WLTime.TypedStack.Code

end OAI
