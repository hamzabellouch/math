import OAI.Combinatorics.VariableWL.Program

namespace OAI

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

namespace Program
variable {Q Γ : Type} {k : ℕ}

 def evolve (P : Program Q Γ k) (s : State Q Γ k) : ℕ → State Q Γ k
  | 0 => s
  | n+1 => (P.step (P.evolve s n)).getD (P.evolve s n)

 theorem evolve_add (P : Program Q Γ k) (s : State Q Γ k) (n m : ℕ) :
    P.evolve s (n+m)=P.evolve (P.evolve s n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (P.step (P.evolve s (n+m))).getD (P.evolve s (n+m)) = _
    rw [ih]
    rfl

 theorem evolve_run (P : Program Q Γ k) (w : Word) (n : ℕ) :
    P.evolve (initial w) n=P.run w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [evolve,run,ih]

 theorem evolve_one (P : Program Q Γ k) {s s' : State Q Γ k} (h : P.step s=some s') :
    P.evolve s 1=s' := by simp only [evolve,h,Option.getD_some]

end Program

 theorem state_ext {Q Γ : Type} {k : ℕ} {s t : State Q Γ k}
    (hc : s.control=t.control) (hh : s.heads=t.heads) (hs : s.cells=t.cells) : s=t := by
  cases s
  cases t
  congr

namespace Stack

inductive Control (Q : Type) (k : ℕ) where
  | read
  | put (b : Bool)
  | back
  | execute (q : Q)
  | pending (q : Q) (acts : Fin (k+1) → Action)
  | output
  deriving Fintype

 def readBit : Symbol PUnit → Option Bool
  | some (.inl b) => some b
  | _ => none

 @[simp] theorem readBit_bit (b : Bool) : readBit (bitSymbol b)=some b := rfl
 @[simp] theorem readBit_none : readBit none=none := rfl
 @[simp] theorem readBit_bind (b : Option Bool) : readBit (b.bind bitSymbol)=b := by
  cases b <;> rfl

 def marker : Symbol PUnit := some (.inr PUnit.unit)

 def instruction (q : Control Q k) (io : Symbol PUnit × Motion)
    (work : Fin (k+1) → Symbol PUnit × Motion) :
    Option (Option (Control Q k) × (Fin (k+2) → Symbol PUnit × Motion)) :=
  some (some q, Fin.cases io work)

 def Machine.program (M : Machine Q k) : Program (Control Q k) PUnit (k+1) where
  transition q cells :=
    match q with
    | none =>
      match readBit (cells 0) with
      | none => instruction (.execute M.start) (none,.stay)
          (fun j => (cells j.succ,.stay))
      | some b => instruction (.put b) (marker,.right)
          (fun j => (cells j.succ,if j=0 then .left else .stay))
    | some .read =>
      match readBit (cells 0) with
      | none => instruction .back (none,.left) (fun j => (cells j.succ,.stay))
      | some b => instruction (.put b) (none,.right)
          (fun j => (cells j.succ,if j=0 then .left else .stay))
    | some (.put b) => instruction .read (cells 0,.stay)
        (fun j => (if j=0 then bitSymbol b else cells j.succ,.stay))
    | some .back =>
      match cells 0 with
      | some (.inr _) => instruction (.execute M.start) (none,.stay)
          (fun j => (cells j.succ,.stay))
      | _ => instruction .back (cells 0,.left) (fun j => (cells j.succ,.stay))
    | some (.execute q) =>
      match M.transition q (fun j => readBit (cells j.succ)) with
      | none => instruction .output (cells 0,.stay) (fun j => (cells j.succ,.stay))
      | some (q',acts) => instruction (.pending q' acts) (cells 0,.stay)
          (fun j => ((acts j).firstWrite (readBit (cells j.succ)),
            (acts j).firstMove (readBit (cells j.succ))))
    | some (.pending q acts) => instruction (.execute q) (cells 0,.stay)
        (fun j => ((acts j).secondWrite (cells j.succ),.stay))
    | some .output =>
      match readBit (cells M.output.succ) with
      | none => none
      | some b => instruction .output (bitSymbol b,.right)
          (fun j => (if j=M.output then none else cells j.succ,
            if j=M.output then .right else .stay))

 def Machine.execState (_M : Machine Q k) (s : State Q k) :
    Computation.State (Control Q k) PUnit (k+1) where
  control := some (.execute s.control)
  heads := Fin.cases 0 (fun j => stackHead (s.tapes j))
  cells := Fin.cases (fun _ => none) (fun j => stackCells (s.tapes j))

 def intermediate (s : Computation.State Q Γ k) (q : Option Q)
    (data : Fin (k+1) → Symbol Γ × Motion) : Computation.State Q Γ k where
  control := q
  heads := fun j => s.heads j + (data j).2.displacement
  cells := fun j i => if i=s.heads j then (data j).1 else s.cells j i

 theorem step_eq_intermediate (P : Program Q Γ k) (s : Computation.State Q Γ k)
    (q : Option Q) (data : Fin (k+1) → Symbol Γ × Motion)
    (h : P.transition s.control (fun j => s.cells j (s.heads j))=some (q,data)) :
    P.step s=some (intermediate s q data) := by
  unfold Program.step
  rw [h]
  rfl

 theorem Machine.execute_two (M : Machine Q k) (s : State Q k)
    (q : Q) (acts : Fin (k+1) → Action)
    (h : M.transition s.control (fun j => (s.tapes j).head?)=some (q,acts)) :
    M.program.evolve (M.execState s) 2=
      M.execState ⟨q,fun j => (acts j).apply (s.tapes j)⟩ := by
  let data : Fin (k+2) → Symbol PUnit × Motion := Fin.cases (none,.stay)
    (fun j => ((acts j).firstWrite (s.tapes j).head?,
      (acts j).firstMove (s.tapes j).head?))
  let mid := intermediate (M.execState s) (some (.pending q acts)) data
  have hs : M.program.step (M.execState s)=some mid := by
    apply step_eq_intermediate
    dsimp only [Machine.program,Machine.execState]
    simp only [Fin.cases_succ,stackCells_head,readBit_bind,h]
    rfl
  have ht : M.program.step mid=some (M.execState ⟨q,fun j => (acts j).apply (s.tapes j)⟩) := by
    let data' : Fin (k+2) → Symbol PUnit × Motion :=
      Fin.cases (mid.cells 0 (mid.heads 0),.stay)
        (fun j => ((acts j).secondWrite (mid.cells j.succ (mid.heads j.succ)),.stay))
    have he : M.program.step mid=some (intermediate mid (some (.execute q)) data') := by
      apply step_eq_intermediate
      rfl
    rw [he]
    apply congrArg some
    apply state_ext
    · rfl
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change (stackHead (s.tapes j)+((acts j).firstMove _).displacement)+0 = _
        rw [add_zero,firstUpdate]
        rfl
    · funext i x
      refine Fin.cases ?_ (fun j => ?_) i
      · change (if x=0+0 then (if 0+0=0 then none else none)
          else if x=0 then none else none)=none
        simp only [ite_self]
      · change (if x=stackHead (s.tapes j)+((acts j).firstMove _).displacement then
          (acts j).secondWrite (if stackHead (s.tapes j)+((acts j).firstMove _).displacement=
            stackHead (s.tapes j) then (acts j).firstWrite _ else
            stackCells (s.tapes j) (stackHead (s.tapes j)+((acts j).firstMove _).displacement))
          else if x=stackHead (s.tapes j) then (acts j).firstWrite _ else stackCells (s.tapes j) x) = _
        rw [firstUpdate]
        exact secondUpdate _ _ _
  simp only [Program.evolve,hs,Option.getD_some,ht]

end Stack
end VariableWL.Computation

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

 theorem typedWordCells_snoc (w : Word) (b : Bool) (i : ℤ) :
    typedWordCells (Γ:=Γ) (w++[b]) i =
      if i=(w.length:ℤ) then bitSymbol b else typedWordCells w i := by
  induction w generalizing i with
  | nil =>
    rw [List.nil_append,typedWordCells_cons]
    simp only [typedWordCells_nil,List.length_nil,Nat.cast_zero]
  | cons a w ih =>
    rw [List.cons_append,typedWordCells_cons,typedWordCells_cons,ih]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    split_ifs <;> first | rfl | (exfalso; omega)

namespace Stack

 def tapeState (q : Option Q) (h : ℤ) (c : ℤ → Symbol Γ) (ws : Fin (k+1) → Word) :
    Computation.State Q Γ (k+1) where
  control := q
  heads := Fin.cases h (fun j => stackHead (ws j))
  cells := Fin.cases c (fun j => stackCells (ws j))

 def firstData (ws : Fin (k+1) → Word) (io : Symbol Γ × Motion)
    (acts : Fin (k+1) → Action) : Fin (k+2) → Symbol Γ × Motion :=
  Fin.cases io (fun j => ((acts j).firstWrite (ws j).head?,(acts j).firstMove (ws j).head?))

 def secondData (s : Computation.State Q Γ (k+1)) (acts : Fin (k+1) → Action) :
    Fin (k+2) → Symbol Γ × Motion :=
  Fin.cases (s.cells 0 (s.heads 0),.stay)
    (fun j => ((acts j).secondWrite (s.cells j.succ (s.heads j.succ)),.stay))

 theorem twoTapeUpdates (q qmid qfinal : Option Q) (h : ℤ) (c : ℤ → Symbol Γ)
    (ws : Fin (k+1) → Word) (io : Symbol Γ × Motion) (acts : Fin (k+1) → Action) :
    let mid := intermediate (tapeState q h c ws) qmid (firstData ws io acts)
    intermediate mid qfinal (secondData mid acts) =
      tapeState qfinal (h+io.2.displacement) (fun i => if i=h then io.1 else c i)
        (fun j => (acts j).apply (ws j)) := by
  dsimp only
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change h+io.2.displacement+0=h+io.2.displacement
      omega
    · change stackHead (ws j)+((acts j).firstMove _).displacement+0=stackHead _
      rw [add_zero,firstUpdate]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=h+io.2.displacement then
        (if h+io.2.displacement=h then io.1 else c (h+io.2.displacement))
        else if x=h then io.1 else c x) = if x=h then io.1 else c x
      split_ifs <;> simp_all
    · change (if x=stackHead (ws j)+((acts j).firstMove _).displacement then
        (acts j).secondWrite (if stackHead (ws j)+((acts j).firstMove _).displacement=
          stackHead (ws j) then (acts j).firstWrite _ else
          stackCells (ws j) (stackHead (ws j)+((acts j).firstMove _).displacement))
        else if x=stackHead (ws j) then (acts j).firstWrite _ else stackCells (ws j) x) = _
      rw [firstUpdate]
      exact secondUpdate _ _ _

 def inputTapes (w : Word) : Fin (k+1) → Word := fun j => if j=0 then w.reverse else []
 def pushInput (b : Bool) : Fin (k+1) → Action := fun j => if j=0 then .push b else .keep

 theorem pushInput_apply (p : Word) (b : Bool) :
    (fun j : Fin (k+1) => (pushInput b j).apply (inputTapes p j))=inputTapes (p++[b]) := by
  funext j
  simp only [pushInput,inputTapes]
  split_ifs <;> simp [Action.apply,List.reverse_append]

 def inputCells (p w : Word) (i : ℤ) : Symbol PUnit :=
  if i=0 then marker else typedWordCells w (i-p.length)

 theorem inputCells_scan (p w : Word) (hp : 0 < p.length) :
    inputCells p w p.length=w.head?.bind bitSymbol := by
  unfold inputCells
  rw [ite_eq_right (by omega),sub_self]
  cases w <;> rfl

 theorem inputCells_zero (p w : Word) : inputCells p w 0=marker := by
  simp only [inputCells,ite_true]

 theorem inputCells_blank (p : Word) (i : ℤ) : inputCells p [] i=
    if i=0 then marker else none := by
  simp only [inputCells,typedWordCells_nil]

 theorem inputCells_next (p w : Word) (b : Bool) (hp : 0 < p.length) (i : ℤ) :
    (if i=p.length then none else inputCells p (b::w) i)=inputCells (p++[b]) w i := by
  unfold inputCells
  rw [typedWordCells_cons]
  simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
  by_cases hz : i=0
  · subst i
    rw [ite_eq_right (by omega),ite_eq_left rfl,ite_eq_left rfl]
  · rw [ite_eq_right hz,ite_eq_right hz]
    by_cases hi : i=p.length
    · subst i
      rw [ite_eq_left rfl]
      have : (p.length:ℤ)-((p.length:ℤ)+1) = -1 := by omega
      rw [this]
      unfold typedWordCells
      rfl
    · rw [ite_eq_right hi,ite_eq_right (by omega)]
      congr 1
      omega

 def Machine.loading (_M : Machine Q k) (p w : Word) :
    Computation.State (Control Q k) PUnit (k+1) :=
  tapeState (some .read) p.length (inputCells p w) (inputTapes p)

 theorem Machine.loading_two (M : Machine Q k) (p w : Word) (b : Bool) (hp : 0 < p.length) :
    M.program.evolve (M.loading p (b::w)) 2=M.loading (p++[b]) w := by
  let io : Symbol PUnit × Motion := (none,.right)
  let mid := intermediate (M.loading p (b::w)) (some (.put b))
    (firstData (inputTapes p) io (pushInput b))
  have hs : M.program.step (M.loading p (b::w))=some mid := by
    apply step_eq_intermediate
    dsimp only [Machine.program,Machine.loading,tapeState]
    simp only [Fin.cases_zero,inputCells_scan p _ hp,List.head?_cons,Option.bind_some,readBit_bit]
    congr 1
    funext j
    change (stackCells (inputTapes p j) (stackHead (inputTapes p j)),
      if j=0 then Motion.left else .stay) = _
    rw [stackCells_head]
    dsimp only [pushInput]
    split_ifs <;> rfl
  have ht : M.program.step mid=some (intermediate mid (some .read) (secondData mid (pushInput b))) := by
    apply step_eq_intermediate
    dsimp only [Machine.program,mid,intermediate]
    congr 1
    funext j
    dsimp only [pushInput]
    split_ifs <;> rfl
  simp only [Program.evolve,hs,Option.getD_some,ht]
  rw [show mid=intermediate (tapeState (some .read) p.length (inputCells p (b::w))
      (inputTapes p)) (some (.put b)) (firstData (inputTapes p) io (pushInput b)) from rfl]
  rw [twoTapeUpdates,pushInput_apply]
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+1=((p++[b]).length:ℤ)
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    · rfl
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · exact inputCells_next p w b hp x
    · rfl

end Stack
end VariableWL.Computation

namespace VariableWL.Computation.Stack

variable {Q : Type} {k : ℕ}

 theorem initial_tapeState (w : Word) :
    Program.initial (Q:=Control Q k) (Γ:=PUnit) (k:=k+1) w =
    tapeState none 0 (typedWordCells w) (inputTapes []) := by
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (0:ℤ)=stackHead (inputTapes [] j)
      simp [inputTapes,stackHead]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (if j.succ=0 then typedWordCells w else fun _ => none) x=stackCells (inputTapes [] j) x
      rw [ite_eq_right (Fin.succ_ne_zero j)]
      simp [inputTapes]

 theorem Machine.initial_two (M : Machine Q k) (b : Bool) (w : Word) :
    M.program.evolve (Program.initial (b::w)) 2=M.loading [b] w := by
  rw [initial_tapeState]
  let start : Computation.State (Control Q k) PUnit (k+1) := tapeState (none : Option (Control Q k)) 0 (typedWordCells (b::w)) (inputTapes [])
  let io : Symbol PUnit × Motion := (marker,.right)
  let mid := intermediate start (some (.put b)) (firstData (inputTapes []) io (pushInput b))
  have hs : M.program.step start=some mid := by
    apply step_eq_intermediate
    change instruction (Control.put (Q:=Q) (k:=k) b) (marker,.right)
      (fun j => (stackCells (inputTapes [] j) (stackHead (inputTapes [] j)),
        if j=0 then Motion.left else .stay)) = _
    congr 1
    funext j
    rw [stackCells_head]
    dsimp only [pushInput]
    split_ifs <;> rfl
  have ht : M.program.step mid=some (intermediate mid (some .read) (secondData mid (pushInput b))) := by
    apply step_eq_intermediate
    dsimp only [Machine.program,mid,intermediate]
    congr 1
    funext j
    dsimp only [pushInput]
    split_ifs <;> rfl
  change M.program.evolve start 2=_
  simp only [Program.evolve,hs,Option.getD_some,ht]
  rw [show mid=intermediate start (some (.put b)) (firstData (inputTapes []) io (pushInput b)) from rfl]
  rw [show start=tapeState (none : Option (Control Q k)) 0 (typedWordCells (b::w)) (inputTapes []) from rfl]
  rw [twoTapeUpdates,pushInput_apply]
  apply state_ext
  · rfl
  · rfl
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then marker else typedWordCells (b::w) x)=inputCells [b] w x
      rw [typedWordCells_cons]
      unfold inputCells
      simp only [List.length_singleton,Nat.cast_one]
      split_ifs <;> rfl
    · rfl

 theorem Machine.loading_all (M : Machine Q k) (p w : Word) (hp : 0 < p.length) :
    M.program.evolve (M.loading p w) (2*w.length)=M.loading (p++w) [] := by
  induction w generalizing p with
  | nil => simp only [List.length_nil,mul_zero,Program.evolve,List.append_nil]
  | cons b w ih =>
    have he : 2*(b::w).length=2+2*w.length := by simp only [List.length_cons]; omega
    rw [he,Program.evolve_add,M.loading_two p w b hp]
    rw [ih (p++[b]) (by simp only [List.length_append,List.length_singleton]; omega)]
    simp only [List.append_assoc,List.singleton_append]

 def Machine.backState (_M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    Computation.State (Control Q k) PUnit (k+1) :=
  tapeState (some .back) n (fun i => if i=0 then marker else none) ws

 theorem Machine.back_zero (M : Machine Q k) (ws : Fin (k+1) → Word) :
    M.program.step (M.backState 0 ws)=some (M.execState ⟨M.start,ws⟩) := by
  unfold Program.step
  change (instruction (Control.execute (k:=k) M.start) (none,.stay)
    (fun j => (stackCells (ws j) (stackHead (ws j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else if x=0 then marker else none)=none
      split_ifs <;> rfl
    · change (if x=stackHead (ws j) then stackCells (ws j) (stackHead (ws j))
        else stackCells (ws j) x)=stackCells (ws j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.back_succ (M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    M.program.step (M.backState (n+1) ws)=some (M.backState n ws) := by
  have hz : ((n+1:ℕ):ℤ)≠0 := by omega
  unfold Program.step
  dsimp only [Machine.program,Machine.backState,tapeState,Fin.cases_zero]
  rw [ite_eq_right hz]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((n+1:ℕ):ℤ)+(-1)=(n:ℤ)
      omega
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=((n+1:ℕ):ℤ) then none else if x=0 then marker else none)=
        if x=0 then marker else none
      split_ifs <;> first | rfl | (exfalso; omega)
    · change (if x=stackHead (ws j) then stackCells (ws j) (stackHead (ws j))
        else stackCells (ws j) x)=stackCells (ws j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.back_all (M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    M.program.evolve (M.backState n ws) (n+1)=M.execState ⟨M.start,ws⟩ := by
  induction n with
  | zero => exact M.program.evolve_one (M.back_zero ws)
  | succ n ih =>
    rw [show n+1+1=1+(n+1) by omega,Program.evolve_add]
    rw [M.program.evolve_one (M.back_succ n ws),ih]

 theorem Machine.loading_end (M : Machine Q k) (p : Word) (hp : 0 < p.length) :
    M.program.step (M.loading p [])=some (M.backState (p.length-1) (inputTapes p)) := by
  unfold Program.step
  dsimp only [Machine.program,Machine.loading,tapeState,Fin.cases_zero]
  rw [inputCells_scan p [] hp]
  change (instruction (Control.back : Control Q k) (none,.left)
    (fun j => (stackCells (inputTapes p j) (stackHead (inputTapes p j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+(-1)=((p.length-1:ℕ):ℤ)
      omega
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=p.length then none else inputCells p [] x)=if x=0 then marker else none
      rw [inputCells_blank]
      split_ifs <;> first | rfl | (exfalso; omega)
    · change (if x=stackHead (inputTapes p j) then stackCells (inputTapes p j) (stackHead (inputTapes p j))
        else stackCells (inputTapes p j) x)=stackCells (inputTapes p j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.initial_empty (M : Machine Q k) :
    M.program.evolve (Program.initial []) 1=M.execState (M.initial []) := by
  apply Program.evolve_one
  rw [initial_tapeState]
  unfold Program.step
  change (instruction (Control.execute (k:=k) M.start) (none,.stay)
    (fun j => (stackCells (inputTapes [] j) (stackHead (inputTapes [] j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else typedWordCells [] x)=none
      simp only [typedWordCells_nil,ite_self]
    · change (if x=stackHead (inputTapes [] j) then stackCells (inputTapes [] j) (stackHead (inputTapes [] j))
        else stackCells (inputTapes [] j) x)=stackCells (inputTapes [] j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.initialize (M : Machine Q k) (w : Word) :
    M.program.run w (3*w.length+1)=M.execState (M.initial w) := by
  rw [← Program.evolve_run]
  cases w with
  | nil => exact M.initial_empty
  | cons b w =>
    have hn : 3*(b::w).length+1=2+(2*w.length+(1+(w.length+1))) := by
      simp only [List.length_cons]; omega
    rw [hn,Program.evolve_add,M.initial_two,Program.evolve_add,
      M.loading_all [b] w (by simp),Program.evolve_add]
    rw [M.program.evolve_one (M.loading_end ([b]++w) (by simp)),
      show ([b]++w).length-1=w.length by simp,M.back_all]
    rfl

end VariableWL.Computation.Stack

end OAI
