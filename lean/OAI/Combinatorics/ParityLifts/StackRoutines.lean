import OAI.Combinatorics.ParityLifts.StackMachine

namespace OAI

namespace ParityWL.Complexity

abbrev Words (t a : ℕ) := Fin (t + 1) → List (StackSymbol a)

def applyOps {t a : ℕ} (ops : Fin (t + 1) → StackOp a) (w : Words t a) : Words t a :=
  fun i => (ops i).apply (w i)

inductive StackExec {Q : Type} {t a : ℕ} (P : StackMachine Q t a) :
    StackConfiguration Q t a → ℕ → StackConfiguration Q t a → Bool → Prop
  | halt (x : StackConfiguration Q t a) (b : Bool) (h : P.output x.state = some b) :
      StackExec P x 0 x b
  | next (x : StackConfiguration Q t a) {n : ℕ} {y : StackConfiguration Q t a} {b : Bool}
      (h : P.output x.state = none) (tail : StackExec P (P.step x) n y b) :
      StackExec P x (n + 1) y b

lemma StackExec.output {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {x y : StackConfiguration Q t a} {n : ℕ} {b : Bool} (h : StackExec P x n y b) :
    P.output y.state = some b := by
  induction h with
  | halt _ _ h => exact h
  | next _ _ _ ih => exact ih

lemma StackExec.iterate {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {x y : StackConfiguration Q t a} {n : ℕ} {b : Bool} (h : StackExec P x n y b) :
    P.step^[n] x = y := by
  induction h with
  | halt => rfl
  | next _ _ _ ih => exact (Function.iterate_succ_apply _ _ _).trans ih

lemma StackExec.map {Q R : Type} {t a : ℕ} {P : StackMachine Q t a} {T : StackMachine R t a}
    (f : StackConfiguration Q t a → StackConfiguration R t a)
    (ho : ∀ x, T.output (f x).state = P.output x.state)
    (hs : ∀ x, P.output x.state = none → T.step (f x) = f (P.step x))
    {x y : StackConfiguration Q t a} {n : ℕ} {b : Bool} (h : StackExec P x n y b) :
    StackExec T (f x) n (f y) b := by
  induction h with
  | halt x b h => exact .halt _ _ ((ho x).trans h)
  | next x h _ ih =>
    apply StackExec.next _ ((ho x).trans h)
    rw [hs x h]
    exact ih

/-- Structured sequential composition; one finite-control step starts the
second routine once the first has returned. No external simulator is presumed. -/
def StackMachine.andThen {Q R : Type} {t a : ℕ}
    (P : StackMachine Q t a) (T : StackMachine R t a) : StackMachine (Q ⊕ R) t a where
  initial := Sum.inl P.initial
  output := fun q => match q with | .inl _ => none | .inr q => T.output q
  transition := fun q x => match q with
    | .inl q => match P.output q with
      | none => let b := P.transition q x; (.inl b.1, b.2)
      | some _ => (.inr T.initial, fun _ => .keep)
    | .inr q => let b := T.transition q x; (.inr b.1, b.2)

def StackConfiguration.inl {Q R : Type} {t a : ℕ} (x : StackConfiguration Q t a) :
    StackConfiguration (Q ⊕ R) t a := ⟨Sum.inl x.state, x.word⟩

def StackConfiguration.inr {Q R : Type} {t a : ℕ} (x : StackConfiguration R t a) :
    StackConfiguration (Q ⊕ R) t a := ⟨Sum.inr x.state, x.word⟩

lemma StackExec.andThen_right {Q R : Type} {t a : ℕ}
    (P : StackMachine Q t a) (T : StackMachine R t a)
    {x y : StackConfiguration R t a} {n : ℕ} {b : Bool} (h : StackExec T x n y b) :
    StackExec (P.andThen T) x.inr n y.inr b := by
  apply StackExec.map StackConfiguration.inr (fun _ => rfl) ?_ h
  intro x hx
  simp only [StackMachine.step, StackMachine.andThen, StackConfiguration.inr, hx]

lemma StackExec.andThen {Q R : Type} {t a : ℕ}
    {P : StackMachine Q t a} {T : StackMachine R t a}
    {x z : StackConfiguration Q t a} {y : StackConfiguration R t a}
    {n m : ℕ} {b c : Bool} (h : StackExec P x n z b)
    (ht : StackExec T ⟨T.initial, z.word⟩ m y c) :
    StackExec (P.andThen T) x.inl (n + 1 + m) y.inr c := by
  induction h with
  | halt x b hx =>
    have hr := ht.andThen_right P T
    have he : (P.andThen T).step x.inl = (⟨T.initial, x.word⟩ : StackConfiguration R t a).inr := by
      simp only [StackMachine.step, StackMachine.andThen, StackConfiguration.inl, hx,
        StackConfiguration.inr, StackOp.apply]
    have hh := StackExec.next x.inl (by rfl : (P.andThen T).output x.inl.state = none)
      (he ▸ hr)
    simpa only [Nat.zero_add, Nat.add_comm 1 m] using hh
  | next x hx h ih =>
    have he : (P.andThen T).step x.inl = (P.step x).inl := by
      simp only [StackMachine.step, StackMachine.andThen, StackConfiguration.inl, hx]
    have hh := StackExec.next x.inl (by rfl : (P.andThen T).output x.inl.state = none)
      (he ▸ ih ht)
    convert hh using 1
    omega

/-- Repeat a returning routine until it returns true, removing the halt marker
on false. Restarting takes one local stack step and does not touch data. -/
def StackMachine.repeat {Q : Type} {t a : ℕ} (P : StackMachine Q t a) : StackMachine Q t a where
  initial := P.initial
  output := fun q => if P.output q = some true then some true else none
  transition := fun q x => match P.output q with
    | none => P.transition q x
    | some _ => (P.initial, fun _ => .keep)

lemma StackExec.repeat_true {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {x y : StackConfiguration Q t a} {n : ℕ} (h : StackExec P x n y true) :
    StackExec P.repeat x n y true := by
  generalize hb : true = b at h
  induction h with
  | halt x b hx => subst b; exact .halt _ _ (by simp [StackMachine.repeat, hx])
  | next x hx h ih =>
    apply StackExec.next _ (by simp [StackMachine.repeat, hx])
    have he : P.repeat.step x = P.step x := by simp [StackMachine.step, StackMachine.repeat, hx]
    rw [he]
    exact ih hb

lemma StackExec.repeat_false {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {x z y : StackConfiguration Q t a} {n m : ℕ}
    (h : StackExec P x n z false)
    (ht : StackExec P.repeat ⟨P.initial, z.word⟩ m y true) :
    StackExec P.repeat x (n + 1 + m) y true := by
  generalize hb : false = b at h
  induction h with
  | halt x b hx =>
    subst b
    have he : P.repeat.step x = ⟨P.initial, x.word⟩ := by
      simp [StackMachine.step, StackMachine.repeat, hx, StackOp.apply]
    have hh := StackExec.next x (by simp [StackMachine.repeat, hx]) (he ▸ ht)
    simpa only [Nat.zero_add, Nat.add_comm 1 m] using hh
  | next x hx h ih =>
    have he : P.repeat.step x = P.step x := by simp [StackMachine.step, StackMachine.repeat, hx]
    have hh := StackExec.next x (by simp [StackMachine.repeat, hx]) (he ▸ ih ht hb)
    convert hh using 1
    omega

/-- One finite-table operation, including a return bit chosen from scanned tops.
All alphabets and control sets of this routine are visibly finite. -/
def primitive {t a : ℕ}
    (ops : (Fin (t + 1) → Option (StackSymbol a)) → Fin (t + 1) → StackOp a)
    (test : (Fin (t + 1) → Option (StackSymbol a)) → Bool) :
    StackMachine (Option Bool) t a where
  initial := none
  output := id
  transition := fun _ x => (some (test x), ops x)

lemma primitive_exec {t a : ℕ}
    (ops : (Fin (t + 1) → Option (StackSymbol a)) → Fin (t + 1) → StackOp a)
    (test : (Fin (t + 1) → Option (StackSymbol a)) → Bool) (w : Words t a) :
    let tops := fun i => (w i).head?
    StackExec (primitive ops test) ⟨none, w⟩ 1
      ⟨some (test tops), applyOps (ops tops) w⟩ (test tops) := by
  dsimp only
  apply StackExec.next _ rfl
  exact StackExec.halt _ _ rfl

def Runs {Q : Type} {t a : ℕ} (P : StackMachine Q t a)
    (w : Words t a) (n : ℕ) (v : Words t a) (b : Bool) : Prop :=
  ∃ q, StackExec P ⟨P.initial, w⟩ n ⟨q, v⟩ b

lemma Runs.andThen {Q R : Type} {t a : ℕ}
    {P : StackMachine Q t a} {T : StackMachine R t a}
    {w v z : Words t a} {n m : ℕ} {b c : Bool}
    (h : Runs P w n v b) (ht : Runs T v m z c) :
    Runs (P.andThen T) w (n + 1 + m) z c := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨r, hr⟩ := ht
  exact ⟨Sum.inr r, hq.andThen hr⟩

lemma Runs.compiled {Q : Type} [Fintype Q] {t a : ℕ}
    {P : StackMachine Q t a} {input : List Bool} {n : ℕ} {v : Words t a} {b : Bool}
    (h : Runs P (fun i => if i.val = 0 then input.map (stackInputSymbol a) else []) n v b) :
    Emits P.compiled input (2 * n) b := by
  rw [P.compiled_emits]
  obtain ⟨q, hq⟩ := h
  exact (congrArg (fun x => P.output x.state) hq.iterate).trans hq.output

end ParityWL.Complexity

namespace ParityWL.Complexity

/-- A finite control-flow chart whose nodes are verified stack routines. -/
structure MacroMachine (Q : Type) (t a : ℕ) where
  Control : Q → Type
  initial : Q
  output : Q → Option Bool
  routine : (q : Q) → StackMachine (Control q) t a
  next : Q → Bool → Q

def MacroMachine.lower {Q : Type} {t a : ℕ} (P : MacroMachine Q t a) :
    StackMachine ((q : Q) × P.Control q) t a where
  initial := ⟨P.initial, (P.routine P.initial).initial⟩
  output := fun q => P.output q.1
  transition := fun ⟨q, r⟩ x => match (P.routine q).output r with
    | none => let v := (P.routine q).transition r x; (⟨q, v.1⟩, v.2)
    | some b => let q' := P.next q b; (⟨q', (P.routine q').initial⟩, fun _ => .keep)

def MacroMachine.lift {Q : Type} {t a : ℕ} (P : MacroMachine Q t a) (q : Q)
    (x : StackConfiguration (P.Control q) t a) :
    StackConfiguration ((q : Q) × P.Control q) t a := ⟨⟨q, x.state⟩, x.word⟩

lemma MacroMachine.exec_routine {Q : Type} {t a : ℕ} (P : MacroMachine Q t a)
    (q : Q) (ho : P.output q = none)
    {x z : StackConfiguration (P.Control q) t a} {n m : ℕ} {b c : Bool}
    {y : StackConfiguration ((q : Q) × P.Control q) t a}
    (h : StackExec (P.routine q) x n z b)
    (ht : StackExec P.lower
      ⟨⟨P.next q b, (P.routine (P.next q b)).initial⟩, z.word⟩ m y c) :
    StackExec P.lower (P.lift q x) (n + 1 + m) y c := by
  induction h with
  | halt x b hx =>
    have he : P.lower.step (P.lift q x) =
        ⟨⟨P.next q b, (P.routine (P.next q b)).initial⟩, x.word⟩ := by
      simp only [StackMachine.step, MacroMachine.lower, MacroMachine.lift, ho, hx, StackOp.apply]
    have hh := StackExec.next (P.lift q x) (by exact ho) (he ▸ ht)
    simpa only [Nat.zero_add, Nat.add_comm 1 m] using hh
  | next x hx _ ih =>
    have he : P.lower.step (P.lift q x) = P.lift q ((P.routine q).step x) := by
      simp only [StackMachine.step, MacroMachine.lower, MacroMachine.lift, ho, hx]
    have hh := StackExec.next (P.lift q x) (by exact ho) (he ▸ ih ht)
    convert hh using 1
    omega

inductive MacroExec {Q : Type} {t a : ℕ} (P : MacroMachine Q t a) :
    Q → Words t a → ℕ → Words t a → Bool → Prop
  | halt (q : Q) (w : Words t a) (b : Bool) (h : P.output q = some b) :
      MacroExec P q w 0 w b
  | next (q : Q) (w : Words t a) {v z : Words t a} {n m : ℕ} {b c : Bool}
      (h : P.output q = none) (hr : Runs (P.routine q) w n v b)
      (tail : MacroExec P (P.next q b) v m z c) :
      MacroExec P q w (n + 1 + m) z c

lemma MacroExec.lower {Q : Type} {t a : ℕ} {P : MacroMachine Q t a}
    {q : Q} {w v : Words t a} {n : ℕ} {b : Bool} (h : MacroExec P q w n v b) :
    ∃ r, StackExec P.lower ⟨⟨q, (P.routine q).initial⟩, w⟩ n ⟨r, v⟩ b := by
  induction h with
  | halt q w b h => exact ⟨_, .halt _ _ h⟩
  | next q w h hr _ ih =>
    obtain ⟨r, hr⟩ := hr
    obtain ⟨s, hs⟩ := ih
    exact ⟨s, P.exec_routine q h hr hs⟩

lemma MacroExec.compiled {Q : Type} [Fintype Q] {t a : ℕ}
    {P : MacroMachine Q t a} [∀ q, Fintype (P.Control q)]
    {input : List Bool} {n : ℕ} {v : Words t a} {b : Bool}
    (h : MacroExec P P.initial
      (fun i => if i.val = 0 then input.map (stackInputSymbol a) else []) n v b) :
    Emits P.lower.compiled input (2 * n) b := by
  exact Runs.compiled h.lower

/-- A finite-table transfer step. The source is popped; a prescribed subset of
other stacks receives its top symbol. An empty source returns true. -/
def transferStep {t a : ℕ} (src : Fin (t + 1)) (dst : Finset (Fin (t + 1))) :
    StackMachine (Option Bool) t a :=
  primitive (fun x i => match x src with
    | none => .keep
    | some c => if i = src then .pop else if i ∈ dst then .push c else .keep)
    (fun x => (x src).isNone)

def transfer {t a : ℕ} (src : Fin (t + 1)) (dst : Finset (Fin (t + 1))) :=
  (transferStep (a := a) src dst).repeat

def transferred {t a : ℕ} (src : Fin (t + 1)) (dst : Finset (Fin (t + 1)))
    (w : Words t a) : Words t a :=
  fun i => if i = src then [] else if i ∈ dst then (w src).reverse ++ w i else w i

lemma transfer_run {t a : ℕ} (src : Fin (t + 1)) (dst : Finset (Fin (t + 1)))
    (w : Words t a) :
    Runs (transfer src dst) w (2 * (w src).length + 1) (transferred src dst w) true := by
  generalize he : w src = l
  induction l generalizing w with
  | nil =>
    have h := primitive_exec (t := t) (a := a)
      (fun x i => match x src with
        | none => .keep
        | some c => if i = src then .pop else if i ∈ dst then .push c else .keep)
      (fun x => (x src).isNone) w
    simp only [he, List.head?_nil, Option.isNone_none] at h
    have hw : applyOps (fun _ => StackOp.keep) w = transferred src dst w := by
      funext i
      simp only [applyOps, StackOp.apply, transferred, he, List.reverse_nil, List.nil_append]
      split_ifs with hi
      · simpa [hi] using he
      · rfl
      · rfl
    change StackExec (transferStep src dst) _ _ _ true at h
    exact ⟨some true, hw ▸ h.repeat_true⟩
  | cons c l ih =>
    let w' := applyOps (fun i => if i = src then .pop else if i ∈ dst then .push c else .keep) w
    have hs : w' src = l := by simp [w', applyOps, StackOp.apply, he]
    obtain ⟨q, hq⟩ := ih w' hs
    have h := primitive_exec (t := t) (a := a)
      (fun x i => match x src with
        | none => .keep
        | some c => if i = src then .pop else if i ∈ dst then .push c else .keep)
      (fun x => (x src).isNone) w
    simp only [he, List.head?_cons, Option.isNone_some] at h
    change StackExec (transferStep src dst) _ 1 ⟨some false, w'⟩ false at h
    have hw : transferred src dst w' = transferred src dst w := by
      funext i
      simp only [transferred, hs, he, List.reverse_cons]
      split_ifs with hi hd
      · rfl
      · simp [w', applyOps, hi, hd, StackOp.apply, List.append_assoc]
      · simp [w', applyOps, hi, hd, StackOp.apply]
    have hh := h.repeat_false hq
    refine ⟨q, ?_⟩
    rw [hw] at hh
    change StackExec (transferStep src dst).repeat ⟨none, w⟩
      (2 * (l.length + 1) + 1) ⟨q, transferred src dst w⟩ true
    convert hh using 1
    omega

/-- Emptying a stack never modifies another stack. -/
lemma clear_run {t a : ℕ} (src : Fin (t + 1)) (w : Words t a) :
    Runs (transfer src ∅) w (2 * (w src).length + 1) (Function.update w src []) true := by
  convert transfer_run src ∅ w using 1
  funext i
  by_cases hi : i = src <;> simp [transferred, Function.update, hi]

end ParityWL.Complexity

end OAI
