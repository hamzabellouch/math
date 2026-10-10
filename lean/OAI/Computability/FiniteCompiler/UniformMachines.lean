import OAI.Computability.FiniteCompiler.TapeFolding

namespace OAI

/-!
Parameterized effective machine realization and uniform finite data.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine
open Compiler.Simulator OneSided Turing Relation
variable {S Γ Q : Type*}

inductive State (Q : Type*) (n : ℕ)
  | start | scan | emit : Fin (n+2) → State Q n
  | rewind | run : Q → State Q n
  deriving DecidableEq, Fintype

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

def machine (p : S) (n : ℕ) : Machine (State Q n) (Bool × Γ) where
  initial := .start
  transition q a := match q with
    | .start => some ⟨.scan,(true,a.2),.stay⟩
    | .scan => if a.2=A.blank then some ⟨.emit ⟨0,by omega⟩,a,.stay⟩
        else some ⟨.scan,a,.right⟩
    | .emit k => if h : k.val<n+1 then
        some ⟨.emit ⟨k.val+1,by omega⟩,(a.1,A.input p),.right⟩
        else some ⟨.rewind,a,.stay⟩
    | .rewind => if a.1 then some ⟨.run M.initial,(false,a.2),.stay⟩
        else some ⟨.rewind,a,.left⟩
    | .run q => (M.transition q a.2).map fun c => ⟨.run c.state,(false,c.write),c.move⟩

def content (w : List S) : ℕ → Γ := Stream'.appendStream' (w.map A.input) (Stream'.const A.blank)
def marked (w : List S) : ℕ → Bool × Γ := fun i => (decide (i=0),content A w i)
def flat (w : List S) : ℕ → Bool × Γ := fun i => (false,content A w i)

omit [DecidableEq Γ] in
 theorem input_ne_blank (a : S) : A.input a≠A.blank := by
  intro h
  have hh := A.output_input a
  rw [h,A.output_blank] at hh
  cases hh

omit [DecidableEq Γ] in
 theorem content_beyond (w : List S) (i : ℕ) (hi : w.length ≤ i) : content A w i=A.blank := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa [content, Stream'.const] using append_at (w.map A.input) (Stream'.const A.blank) j

omit [DecidableEq Γ] in
 theorem content_before (w : List S) (i : ℕ) (hi : i<w.length) :
    content A w i=A.input w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih i (by simpa using hi)

omit [DecidableEq Γ] in
 theorem marked_write (w : List S) (p : S) :
    Function.update (marked A w) w.length (decide (w.length=0),A.input p)=marked A (w++[p]) := by
  funext i
  apply Prod.ext
  · by_cases h : i=w.length
    · subst i; simp [marked]
    · simp [Function.update_of_ne h,marked]
  · by_cases h : i<w.length
    · have hn : i≠w.length := Nat.ne_of_lt h
      rw [Function.update_of_ne hn]
      change content A w i=content A (w++[p]) i
      rw [content_before A w i h,content_before A _ i (by simp; omega)]
      congr 1
      simp [List.getElem_append_left h]
    · by_cases he : i=w.length
      · subst i
        rw [Function.update_self]
        change A.input p=content A (w++[p]) w.length
        rw [content_before A _ _ (by simp)]
        simp
      · rw [Function.update_of_ne he]
        change content A w i=content A (w++[p]) i
        rw [content_beyond A w i (by omega),content_beyond A _ i (by simp; omega)]

omit [DecidableEq Γ] in
 theorem marked_clear (w : List S) :
    Function.update (marked A w) 0 (false,content A w 0)=flat A w := by
  funext i
  by_cases hi : i=0
  · subst i; simp [flat]
  · simp [marked,flat,hi]

variable (p : S) (n : ℕ)

 theorem start_step (w : List S) :
    step (machine A M p n) ⟨.start,0,flat A w⟩=some ⟨.scan,0,marked A w⟩ := by
  simp only [step,machine,flat,Option.map_some]
  congr 2
  funext i
  by_cases hi : i=0
  · subst i; simp [marked]
  · simp [marked,flat,hi]

 theorem scan_step (w : List S) (i : ℕ) (hi : i<w.length) :
    step (machine A M p n) ⟨.scan,i,marked A w⟩=some ⟨.scan,i+1,marked A w⟩ := by
  have hb : content A w i≠A.blank := by rw [content_before A w i hi]; exact input_ne_blank A _
  simp only [step,machine,marked,ite_eq_right hb,Option.map_some]
  congr 2
  exact Function.update_eq_self _ _

 theorem scan_end (w : List S) :
    step (machine A M p n) ⟨.scan,w.length,marked A w⟩=
      some ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩ := by
  simp only [step,machine,marked,content_beyond A w w.length le_rfl,↓reduceIte,Option.map_some]
  have he : (decide (w.length=0),A.blank)=marked A w w.length := by
    simp [marked,content_beyond A w w.length le_rfl]
  rw [he,Function.update_eq_self]

 theorem scan_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.scan,0,marked A w⟩ ⟨.scan,w.length,marked A w⟩ := by
  have h (i : ℕ) (hi : i ≤ w.length) :
      ReflTransGen (fun a b => step (machine A M p n) a=some b)
        ⟨.scan,0,marked A w⟩ ⟨.scan,i,marked A w⟩ := by
    induction i with
    | zero => exact .refl
    | succ i ih => exact (ih (by omega)).tail (scan_step A M p n w i (by omega))
  exact h _ le_rfl

 theorem emit_step (w : List S) (k : Fin (n+2)) (hk : k.val<n+1) :
    step (machine A M p n) ⟨.emit k,w.length,marked A w⟩=
      some ⟨.emit ⟨k.val+1,by omega⟩,(w++[p]).length,marked A (w++[p])⟩ := by
  simp only [step,machine,dite_eq_left hk,marked,Option.map_some,List.length_append,List.length_singleton]
  congr 2
  exact marked_write A w p

 theorem emit_end (w : List S) :
    step (machine A M p n) ⟨.emit ⟨n+1,by omega⟩,w.length,marked A w⟩=
      some ⟨.rewind,w.length,marked A w⟩ := by
  simp only [step,machine,dite_eq_right (Nat.lt_irrefl (n+1)),Option.map_some]
  rw [Function.update_eq_self]

 theorem emit_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩
      ⟨.emit ⟨n+1,by omega⟩,(w++List.replicate (n+1) p).length,
        marked A (w++List.replicate (n+1) p)⟩ := by
  have h (i : ℕ) (hi : i<n+2) :
      ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩
      ⟨.emit ⟨i,hi⟩,(w++List.replicate i p).length,marked A (w++List.replicate i p)⟩ := by
    induction i with
    | zero => simpa using (ReflTransGen.refl (a:= (⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩ : Cfg _ (State Q n))))
    | succ i ih =>
      have hh := (ih (by omega)).tail (emit_step A M p n (w++List.replicate i p) ⟨i,by omega⟩ (by change i<n+1; omega))
      simpa only [List.replicate_succ',List.append_assoc] using hh
  exact h _ (by omega)

 theorem rewind_step (w : List S) (i : ℕ) :
    step (machine A M p n) ⟨.rewind,i+1,marked A w⟩=some ⟨.rewind,i,marked A w⟩ := by
  simp only [step,machine,marked,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,decide_false,
    Bool.false_eq_true, ↓reduceIte,Nat.add_sub_cancel,Option.map_some]
  rw [show (false,content A w (i+1))=marked A w (i+1) by simp [marked]]
  rw [Function.update_eq_self]

 theorem rewind_run (w : List S) (i : ℕ) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.rewind,i,marked A w⟩ ⟨.rewind,0,marked A w⟩ := by
  induction i with
  | zero => exact .refl
  | succ i ih => exact ReflTransGen.head (rewind_step A M p n w i) ih

 theorem rewind_end (w : List S) :
    step (machine A M p n) ⟨.rewind,0,marked A w⟩=some ⟨.run M.initial,0,flat A w⟩ := by
  simp only [step,machine,marked,decide_true,↓reduceIte,Option.map_some]
  congr 2
  exact marked_clear A w

 theorem initialize_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.start,0,flat A w⟩
      ⟨.run M.initial,0,flat A (w++List.replicate (n+1) p)⟩ := by
  have ht : ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.start,0,flat A w⟩ ⟨.scan,0,marked A w⟩ := .single (start_step A M p n w)
  exact ((((ht.trans (scan_run A M p n w)).tail
    (scan_end A M p n w)).trans (emit_run A M p n w)).tail
      (emit_end A M p n _)).trans ((rewind_run A M p n _ _).tail (rewind_end A M p n _))

def lift (c : Cfg Γ Q) : Cfg (Bool × Γ) (State Q n) :=
  ⟨.run c.state,c.pos,fun i => (false,c.cell i)⟩

 theorem step_lift (c : Cfg Γ Q) :
    step (machine A M p n) (lift n c)=(step M c).map (lift n) := by
  simp only [step,machine,lift,Option.map_map]
  congr 1
  funext cmd
  simp only [Function.comp_apply]
  congr 1
  funext i
  by_cases hi : i=c.pos
  · subst i; simp
  · simp [Function.update_of_ne hi]

 theorem lift_respects : StateTransition.Respects (step M) (step (machine A M p n))
    (fun a b => lift n a=b) := by
  rintro c _ rfl
  rw [step_lift]
  cases hc : step M c with
  | none => rfl
  | some d => exact ⟨lift n d,rfl,TransGen.single (by rw [step_lift,hc]; rfl)⟩

 theorem eval_lift (c : Cfg Γ Q) :
    StateTransition.eval (step (machine A M p n)) (lift n c)=
      (StateTransition.eval (step M) c).map (lift n) :=
  StateTransition.tr_eval' _ _ _ (lift_respects A M p n) c

 theorem eval_initialized (w : List S) :
    StateTransition.eval (step (machine A M p n)) ⟨.start,0,flat A w⟩=
      (StateTransition.eval (step M)
        ⟨M.initial,0,content A (w++List.replicate (n+1) p)⟩).map (lift n) := by
  have hi : StateTransition.Reaches (step (machine A M p n))
    ⟨.start,0,flat A w⟩ ⟨.run M.initial,0,flat A (w++List.replicate (n+1) p)⟩ :=
    initialize_run A M p n w
  rw [StateTransition.reaches_eval hi]
  exact eval_lift A M p n
    ⟨M.initial,0,content A (w++List.replicate (n+1) p)⟩

def alphabet : Alphabet S (Bool × Γ) where
  blank := (false,A.blank)
  input s := (false,A.input s)
  output x := if x.1 then none else A.output x.2
  output_input s := A.output_input s
  output_blank := A.output_blank

omit [DecidableEq Γ] in
 theorem output_decode (hA : ∀ g a, A.output g=some a → g=A.input a) :
    ∀ g a, (alphabet A).output g=some a → g=(alphabet A).input a := by
  rintro ⟨b,g⟩ a h
  cases b with
  | true => simp [alphabet] at h
  | false => exact congrArg (false,·) (hA g a h)

omit [DecidableEq Γ] in
 theorem initial_view (w : List S) :
    view (interpret A (initialTape A M w))=⟨M.initial,0,content A w⟩ := by
  simp [view,initialTape,interpret,semanticContent,filledWork,Function.comp_def,content]

omit [DecidableEq Γ] in
 theorem returns_iff (w out : List S) :
    (∃ c, ReflTransGen (UnboundedStep A M) (initialTape A M w) c ∧
      Halted A M c ∧ Returns A c out) ↔
    (∃ c, c ∈ StateTransition.eval (step M) ⟨M.initial,0,content A w⟩ ∧
      ∃ t, c.cell=Stream'.appendStream' (out.map A.input) (Stream'.cons A.blank t)) := by
  constructor
  · rintro ⟨c,hc,hh,ho⟩
    have he : interpret A c ∈ StateTransition.eval (semanticStep M)
        (interpret A (initialTape A M w)) :=
      StateTransition.mem_eval.mpr ⟨unboundedRun_interpret A M hc,
        (semantic_halted_iff A M c).mpr hh⟩
    obtain ⟨d,hd,he⟩ := StateTransition.tr_eval_rev (OneSided.respects M) (initial_view A M w) he
    exact ⟨d,he,by rw [←hd]; exact returns_interpret A ho⟩
  · rintro ⟨c,hc,ho⟩
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval (OneSided.respects M) (initial_view A M w) hc
    obtain ⟨hr,hh⟩ := StateTransition.mem_eval.mp he
    obtain ⟨d,hd,hds⟩ := semanticRun_lift A M hr
    refine ⟨d,hd,?_,?_⟩
    · apply (semantic_halted_iff A M d).mp
      rw [hds]; exact hh
    · apply (semanticReturns_iff A).mp
      rw [hds]
      rw [←hs] at ho
      exact ho

omit [DecidableEq Γ] in
 theorem lift_returns (c : Cfg Γ Q) (out : List S) :
    (∃ t, (lift n c).cell=Stream'.appendStream' (out.map (alphabet A).input)
        (Stream'.cons (alphabet A).blank t)) ↔
    (∃ t, c.cell=Stream'.appendStream' (out.map A.input) (Stream'.cons A.blank t)) := by
  have hm (l : List Γ) (t : Stream' Γ) :
      (fun i => (false,Stream'.appendStream' l t i))=
        Stream'.appendStream' (l.map (false,·)) (fun i => (false,t i)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      funext i; cases i with
      | zero => rfl
      | succ i => exact congrFun ih i
  have hs (l : List (Bool × Γ)) (t : Stream' (Bool × Γ)) :
      (fun i => (Stream'.appendStream' l t i).2)=
        Stream'.appendStream' (l.map Prod.snd) (fun i => (t i).2) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      funext i; cases i with
      | zero => rfl
      | succ i => exact congrFun ih i
  constructor
  · rintro ⟨t,h⟩
    have hh := congrArg (fun f : ℕ → Bool × Γ => fun i => (f i).2) h
    rw [hs] at hh
    refine ⟨fun i => (t i).2,?_⟩
    have ht : (fun i => (Stream'.cons (alphabet A).blank t i).2)=
        Stream'.cons A.blank (fun i => (t i).2) := by
      funext i; cases i <;> rfl
    rw [ht] at hh
    simpa only [lift,alphabet,List.map_map,Function.comp_def] using hh
  · rintro ⟨t,h⟩
    refine ⟨fun i => (false,t i),?_⟩
    change (fun i => (false,c.cell i))=_
    rw [h,hm]
    simp only [List.map_map,Function.comp_def,alphabet]
    congr 1
    funext i; cases i <;> rfl

 theorem realizes {f : List S → Part (List S)} (hM : Compiler.Word.Realizes A M f) :
    Compiler.Word.Realizes (alphabet A) (machine A M p n)
      (fun w => f (w++List.replicate (n+1) p)) := by
  intro w out
  rw [returns_iff]
  have hi : content (alphabet A) w=flat A w := by
    funext i
    induction w generalizing i with
    | nil => rfl
    | cons a w ih => cases i with
      | zero => rfl
      | succ i => exact ih i
  change out ∈ f (w++List.replicate (n+1) p) ↔ _
  rw [hi]
  change out ∈ f _ ↔ ∃ c, c ∈ StateTransition.eval (step (machine A M p n))
    ⟨.start,0,flat A w⟩ ∧ _
  rw [eval_initialized]
  constructor
  · intro ho
    obtain ⟨c,hc,hr⟩ := (returns_iff A M _ out).mp ((hM _ _).mp ho)
    exact ⟨lift n c,Part.mem_map _ hc,(lift_returns A n c out).mpr hr⟩
  · rintro ⟨c,hc,hr⟩
    obtain ⟨d,hd,rfl⟩ := (Part.mem_map_iff _).mp hc
    exact (hM _ _).mpr ((returns_iff A M _ out).mpr
      ⟨d,hd,(lift_returns A n d out).mp hr⟩)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode
open Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

/-- A common, countably coded state space for all unary-initialized programs. -/
abbrev Control (Q : Type*) := ℕ ⊕ Q

def encode (n : ℕ) : State Q n → Control Q
  | .start => .inl 0
  | .scan => .inl 1
  | .rewind => .inl 2
  | .emit k => .inl (k.val+3)
  | .run q => .inr q

def decode (n : ℕ) : Control Q → Option (State Q n)
  | .inr q => some (.run q)
  | .inl 0 => some .start
  | .inl 1 => some .scan
  | .inl 2 => some .rewind
  | .inl (k+3) => if h : k<n+2 then some (.emit ⟨k,h⟩) else none

@[simp] theorem decode_encode (n : ℕ) (q : State Q n) : decode n (encode n q)=some q := by
  cases q <;> simp [encode,decode]

 theorem encode_injective (n : ℕ) : Function.Injective (encode (Q := Q) n) := by
  intro a b h
  have h' := congrArg (decode n) h
  simpa only [decode_encode, Option.some.injEq] using h'

abbrev Cmd (Q Γ : Type*) := Control Q × ((Bool×Γ) × Move)

def encodeCommand (n : ℕ) (c : Command (State Q n) (Bool×Γ)) : Cmd Q Γ :=
  (encode n c.state,c.write,c.move)

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

def transition (n : ℕ) (q : Control Q) (a : Bool×Γ) : Option (Cmd Q Γ) := match q with
  | .inr r => (M.transition r a.2).map fun c => (.inr c.state,(false,c.write),c.move)
  | .inl k => if k=0 then some (.inl 1,(true,a.2),.stay)
    else if k=1 then if a.2=A.blank then some (.inl 3,a,.stay) else some (.inl 1,a,.right)
    else if k=2 then if a.1 then some (.inr M.initial,(false,a.2),.stay)
      else some (.inl 2,a,.left)
    else if k-3<n+2 then if k-3<n+1 then some (.inl (k+1),(a.1,A.input p),.right)
      else some (.inl 2,a,.stay)
    else none

 theorem transition_encode (n : ℕ) (q : State Q n) (a : Bool×Γ) :
    transition A M p n (encode n q) a=
      ((machine A M p n).transition q a).map (encodeCommand n) := by
  cases q with
  | start => rfl
  | scan => simp [transition,encode,machine]; split <;> rfl
  | rewind => simp [transition,encode,machine]; split <;> rfl
  | run q => simp [transition,encode,machine,Option.map_map,encodeCommand,Function.comp_def]
  | emit k =>
    have h0 : k.val+3≠0 := by omega
    have h1 : k.val+3≠1 := by omega
    have h2 : k.val+3≠2 := by omega
    simp only [transition,encode,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,Nat.add_sub_cancel,
      ite_eq_left k.isLt,machine]
    split <;> simp_all [encodeCommand,encode]

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]
noncomputable instance : Primcodable Move := Primcodable.ofEquiv (Fin (Fintype.card Move)) (Fintype.equivFin Move)

 theorem primrec_transition : Primrec (fun x : (ℕ × Control Q) × (Bool×Γ) =>
    transition A M p x.1.1 x.1.2 x.2) := by
  let X := (ℕ × Control Q) × (Bool×Γ)
  have hn : Primrec (fun x : X => x.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun x : X => x.2) := Primrec.snd
  have hbranch : Primrec (fun z : X × ℕ =>
      if z.2=0 then (some (Sum.inl 1,(true,z.1.2.2),Move.stay) : Option (Cmd Q Γ))
      else if z.2=1 then if z.1.2.2=A.blank then some (.inl 3,z.1.2,Move.stay)
        else some (.inl 1,z.1.2,Move.right)
      else if z.2=2 then if z.1.2.1 then some (.inr M.initial,(false,z.1.2.2),Move.stay)
        else some (.inl 2,z.1.2,Move.left)
      else if z.2-3<z.1.1.1+2 then if z.2-3<z.1.1.1+1 then
        some (.inl (z.2+1),(z.1.2.1,A.input p),Move.right)
        else some (.inl 2,z.1.2,Move.stay)
      else none) := by
    have hz : Primrec (fun z : X × ℕ => z.1.2) := ha.comp Primrec.fst
    have mk (c : Control Q) (mv : Move) : Primrec (fun z : X × ℕ => some (c,z.1.2,mv)) :=
      Primrec.option_some.comp ((Primrec.const c).pair (hz.pair (Primrec.const mv)))
    have hemit : Primrec (fun z : X × ℕ =>
        some ((Sum.inl (z.2+1) : Control Q),(z.1.2.1,A.input p),Move.right)) :=
      Primrec.option_some.comp ((Primrec.sumInl.comp (Primrec.succ.comp Primrec.snd)).pair
        (((Primrec.fst.comp hz).pair (Primrec.const _)).pair (Primrec.const _)))
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      ((Primrec.dom_finite (fun a : Bool×Γ =>
        (some (.inl 1,(true,a.2),Move.stay) : Option (Cmd Q Γ)))).comp hz)
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      ((Primrec.dom_finite (fun a : Bool×Γ => if a.2=A.blank then
        (some (.inl 3,a,Move.stay) : Option (Cmd Q Γ)) else some (.inl 1,a,Move.right))).comp hz)
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 2))
      ((Primrec.dom_finite (fun a : Bool×Γ => if a.1 then
        (some (.inr M.initial,(false,a.2),Move.stay) : Option (Cmd Q Γ)) else some (.inl 2,a,Move.left))).comp hz)
    exact Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 3))
      (Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.const 2)))
      (Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 3))
        (Primrec.succ.comp (hn.comp Primrec.fst))) hemit (mk (.inl 2) .stay)) (Primrec.const none)
  exact (Primrec.sumCasesOn (Primrec.snd.comp Primrec.fst) hbranch.to₂
    ((Primrec.dom_finite (fun z : Q × (Bool×Γ) =>
      (M.transition z.1 z.2.2).map fun c =>
        ((Sum.inr c.state : Control Q),(false,c.write),c.move))).comp
          (Primrec.snd.pair (ha.comp Primrec.fst))).to₂).of_eq fun x => by
            cases x.1.2 <;> rfl

noncomputable def support (n : ℕ) : List (Control Q) :=
  ((List.range (n+5)).map Sum.inl) ++ (((Finset.univ : Finset Q).toList).map Sum.inr)

omit [Primcodable Q] in
 theorem mem_support (n : ℕ) (q : State Q n) : encode n q ∈ support (Q := Q) n := by
  cases q <;> simp [support,encode]

 theorem primrec_support : Primrec (support (Q := Q)) := by
  exact Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 5)))
      (Primrec.sumInl.comp Primrec.snd).to₂) (Primrec.const _)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {P α : Type*} [Primcodable P] [Primcodable α] [DecidableEq α]

omit [DecidableEq α] in
/-- Finite weak-component search is primitive recursive uniformly in a
    primitive-recursive edge table, not just separately at every table. -/
theorem primrec_expand_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : P × List α × List α => expand (r x.1) x.2.1 x.2.2) := by
  apply Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
  apply primrec_listFilter (Primrec.fst.comp Primrec.snd)
  unfold Primrec₂
  apply primrec_listAny (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  unfold Primrec₂
  let X := ((P × List α × List α) × α) × α
  have hp : Primrec (fun x : X => x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun x : X => x.2) := Primrec.snd
  have hb : Primrec (fun x : X => x.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.or.comp (hr.comp (hp.pair (ha.pair hb))) (hr.comp (hp.pair (hb.pair ha)))

omit [DecidableEq α] in
theorem primrec_search_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : (P × List α × α) × ℕ => search (r x.1.1) x.1.2.1 x.1.2.2 x.2) := by
  change Primrec₂ (fun (x : P × List α × α) n => search (r x.1) x.2.1 x.2.2 n)
  exact (Primrec.nat_rec
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    ((primrec_expand_family hr).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.snd)))).to₂).of_eq
            (fun x n => by induction n <;> simp_all [search])

omit [DecidableEq α] in
theorem primrec_component_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : P × List α × α => component (r x.1) x.2.1 x.2.2) :=
  (primrec_search_family hr).comp
    (Primrec.id.pair (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))

end FiniteAlgebraicEnvelopes.Effect.Graph

end OAI
