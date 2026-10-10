import OAI.Combinatorics.VariableWL.ProductCellular

namespace OAI

namespace VariableWL.Computation

variable {Γ : Type}

abbrev Symbol (Γ : Type) := Option (Bool ⊕ Γ)

def bitSymbol (b : Bool) : Symbol Γ := some (.inl b)

def typedWordCells (w : Word) (i : ℤ) : Symbol Γ :=
  if 0 ≤ i then w[i.toNat]?.map bitSymbol |>.join else none

structure Program (Q Γ : Type) (k : ℕ) where
  transition : Option Q → (Fin (k+1) → Symbol Γ) →
    Option (Option Q × (Fin (k+1) → Symbol Γ × Motion))

structure State (Q Γ : Type) (k : ℕ) where
  control : Option Q
  heads : Fin (k+1) → ℤ
  cells : Fin (k+1) → ℤ → Symbol Γ

theorem configuration_ext {M : Machine} {a b : Configuration M}
    (hc : a.control=b.control) (hh : a.heads=b.heads) (hs : a.cells=b.cells) : a=b := by
  cases a
  cases b
  congr

namespace Program
variable {Q Γ : Type} {k : ℕ}

 def initial (w : Word) : State Q Γ k where
  control := none
  heads := fun _ => 0
  cells := fun j => if j=0 then typedWordCells w else fun _ => none

 def step (P : Program Q Γ k) (s : State Q Γ k) : Option (State Q Γ k) :=
  (P.transition s.control (fun j => s.cells j (s.heads j))).map fun data =>
    { control := data.1
      heads := fun j => s.heads j + (data.2 j).2.displacement
      cells := fun j i => if i=s.heads j then (data.2 j).1 else s.cells j i }

 def run (P : Program Q Γ k) (w : Word) : ℕ → State Q Γ k
  | 0 => initial w
  | n+1 => (P.step (P.run w n)).getD (P.run w n)

 def OutputsWithin (P : Program Q Γ k) (w out : Word) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, P.step (P.run w t)=none ∧
    (P.run w t).cells 0 = typedWordCells out

noncomputable section
variable [Fintype Q] [Fintype Γ]

 def controlCode : Option Q → Fin (Fintype.card Q+1)
  | none => ⟨0, by omega⟩
  | some q => ⟨(Fintype.equivFin Q q).val+1, by omega⟩

 def symbolCode : Symbol Γ → Fin (Fintype.card Γ+3)
  | none => ⟨0, by omega⟩
  | some (.inl false) => ⟨1, by omega⟩
  | some (.inl true) => ⟨2, by omega⟩
  | some (.inr a) => ⟨(Fintype.equivFin Γ a).val+3, by omega⟩

 theorem controlCode_injective : Function.Injective (controlCode (Q:=Q)) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some q => have := congrArg Fin.val h; dsimp [controlCode] at this; omega
  | some a => cases b with
    | none => have := congrArg Fin.val h; dsimp [controlCode] at this; omega
    | some b =>
      congr 1
      apply (Fintype.equivFin Q).injective
      apply Fin.ext
      have := congrArg Fin.val h
      simpa only [controlCode, Nat.add_right_cancel_iff] using this

 theorem symbolCode_injective : Function.Injective (symbolCode (Γ:=Γ)) := by
  intro a b h
  have hv := congrArg Fin.val h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b with
      | inl b => cases b
                 · change 0=1 at hv; omega
                 · change 0=2 at hv; omega
      | inr b => change 0=(Fintype.equivFin Γ b).val+3 at hv; omega
  | some a => cases b with
    | none => cases a with
      | inl a => cases a
                 · change 1=0 at hv; omega
                 · change 2=0 at hv; omega
      | inr a => change (Fintype.equivFin Γ a).val+3=0 at hv; omega
    | some b => cases a with
      | inl a => cases b with
        | inl b => cases a <;> cases b
                   · rfl
                   · change 1=2 at hv; omega
                   · change 2=1 at hv; omega
                   · rfl
        | inr b => cases a
                   · change 1=(Fintype.equivFin Γ b).val+3 at hv; omega
                   · change 2=(Fintype.equivFin Γ b).val+3 at hv; omega
      | inr a => cases b with
        | inl b => cases b
                   · change (Fintype.equivFin Γ a).val+3=1 at hv; omega
                   · change (Fintype.equivFin Γ a).val+3=2 at hv; omega
        | inr b =>
          congr 2
          apply (Fintype.equivFin Γ).injective
          apply Fin.ext
          change (Fintype.equivFin Γ a).val+3=(Fintype.equivFin Γ b).val+3 at hv
          omega

 def controlDecode := Function.invFun (controlCode (Q:=Q))
 def symbolDecode := Function.invFun (symbolCode (Γ:=Γ))

 @[simp] theorem control_roundtrip (q : Option Q) : controlDecode (controlCode q)=q :=
  Function.leftInverse_invFun controlCode_injective q
 @[simp] theorem symbol_roundtrip (a : Symbol Γ) : symbolDecode (symbolCode a)=a :=
  Function.leftInverse_invFun symbolCode_injective a

 def compile (P : Program Q Γ k) : Machine where
  states := Fintype.card Q
  workSymbols := Fintype.card Γ
  extraTapes := k
  transition := fun q as =>
    (P.transition (controlDecode q) (fun j => symbolDecode (as j))).map fun d =>
      (controlCode d.1, fun j => (symbolCode (d.2 j).1, (d.2 j).2))

 def encodeState (P : Program Q Γ k) (s : State Q Γ k) : Configuration P.compile where
  control := controlCode s.control
  heads := s.heads
  cells := fun j i => symbolCode (s.cells j i)

 theorem encodeWord (w : Word) (i : ℤ) :
    symbolCode (typedWordCells (Γ:=Γ) w i)=wordCells (Fintype.card Γ) w i := by
  unfold typedWordCells wordCells
  split_ifs
  · cases w[i.toNat]? with
    | none => rfl
    | some b => cases b <;> rfl
  · rfl

 theorem encode_initial (P : Program Q Γ k) (w : Word) :
    P.encodeState (initial w)=VariableWL.initial P.compile w := by
  apply configuration_ext <;> try rfl
  funext j i
  change symbolCode ((if j=0 then typedWordCells w else fun _ => none) i) =
    (if j=0 then wordCells _ w else fun _ => 0) i
  split_ifs with h
  · exact encodeWord w i
  · rfl

 theorem encode_step (P : Program Q Γ k) (s : State Q Γ k) :
    VariableWL.step P.compile (P.encodeState s)=(P.step s).map P.encodeState := by
  unfold VariableWL.step step
  change ((P.transition (controlDecode (controlCode s.control))
    (fun j => symbolDecode (symbolCode (s.cells j (s.heads j))))).map _).map _ = _
  simp only [control_roundtrip,symbol_roundtrip,Option.map_map]
  cases P.transition s.control (fun j => s.cells j (s.heads j)) with
  | none => rfl
  | some data =>
    apply congrArg some
    apply configuration_ext <;> try rfl
    funext j i
    change (if i=s.heads j then symbolCode (data.2 j).1 else symbolCode (s.cells j i)) =
      symbolCode (if i=s.heads j then (data.2 j).1 else s.cells j i)
    split_ifs <;> rfl

 theorem encode_run (P : Program Q Γ k) (w : Word) (t : ℕ) :
    VariableWL.run P.compile w t=P.encodeState (P.run w t) := by
  induction t with
  | zero => exact (P.encode_initial w).symm
  | succ t ih =>
    simp only [VariableWL.run,run,ih,P.encode_step]
    cases P.step (P.run w t) <;> rfl

 theorem compile_outputs (P : Program Q Γ k) {w out : Word} {T : ℕ}
    (h : P.OutputsWithin w out T) : VariableWL.OutputsWithin P.compile w out T := by
  obtain ⟨t,ht,halt,hout⟩ := h
  refine ⟨t,ht,?_,?_⟩
  · rw [P.encode_run,P.encode_step,halt]
    rfl
  · rw [P.encode_run]
    funext i
    change symbolCode ((P.run w t).cells 0 i)=wordCells _ out i
    rw [congrFun hout i]
    exact encodeWord out i

end
end Program
end VariableWL.Computation

namespace VariableWL.Computation

variable {Γ : Type}

 theorem typedWordCells_nil (i : ℤ) : typedWordCells (Γ:=Γ) [] i=none := by
  unfold typedWordCells
  split_ifs <;> rfl

 theorem typedWordCells_cons (b : Bool) (w : Word) (i : ℤ) :
    typedWordCells (Γ:=Γ) (b::w) i =
      if i=0 then bitSymbol b else typedWordCells w (i-1) := by
  by_cases hi : i=0
  · subst i
    rfl
  · rw [ite_eq_right hi]
    by_cases hn : i < 0
    · unfold typedWordCells
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    · obtain ⟨n,hnat⟩ : ∃ n : ℕ, i=(n+1:ℕ) := by
        refine ⟨i.toNat-1,?_⟩
        have := Int.toNat_of_nonneg (by omega : 0 ≤ i)
        omega
      subst i
      unfold typedWordCells
      rw [ite_eq_left (by omega),ite_eq_left (by omega)]
      have hsub : ((n+1:ℕ):ℤ)-1=(n:ℤ) := by omega
      simp only [hsub,Int.toNat_natCast,List.getElem?_cons_succ]

 def stackCells (w : Word) (i : ℤ) : Symbol Γ := typedWordCells w (i+w.length)
 def stackHead (w : Word) : ℤ := -(w.length:ℤ)

 @[simp] theorem stackCells_nil (i : ℤ) : stackCells (Γ:=Γ) [] i=none :=
  typedWordCells_nil _

 theorem stackCells_cons (b : Bool) (w : Word) (i : ℤ) :
    stackCells (Γ:=Γ) (b::w) i =
      if i=stackHead w-1 then bitSymbol b else stackCells w i := by
  unfold stackCells
  rw [typedWordCells_cons]
  apply if_congr
  · simp only [List.length_cons,stackHead]
    omega
  · rfl
  · congr 1
    simp only [List.length_cons]
    omega

 theorem stackCells_head (w : Word) : stackCells (Γ:=Γ) w (stackHead w)=
    w.head?.bind bitSymbol := by
  cases w with
  | nil => simp
  | cons b w =>
    rw [stackCells_cons,ite_eq_left]
    · rfl
    · simp only [stackHead,List.length_cons]
      omega

 theorem stackCells_below (w : Word) (i : ℤ) (h : i < stackHead w) :
    stackCells (Γ:=Γ) w i=none := by
  unfold stackCells typedWordCells
  rw [ite_eq_right]
  unfold stackHead at h
  omega

 theorem stackCells_nonnegative (w : Word) (i : ℤ) (h : 0 ≤ i) :
    stackCells (Γ:=Γ) w i=none := by
  unfold stackCells typedWordCells
  rw [ite_eq_left (by omega)]
  rw [List.getElem?_eq_none (by omega)]
  rfl

namespace Stack

inductive Action where
  | keep | pop | push (b : Bool)
  deriving DecidableEq,Fintype

 def Action.apply : Action → Word → Word
  | .keep,w => w
  | .pop,w => w.tail
  | .push b,w => b::w

 def Action.firstMove : Action → Option Bool → Motion
  | .push _,_ => .left
  | .pop,some _ => .right
  | _,_ => .stay

 def Action.firstWrite (a : Action) (top : Option Bool) : Symbol Γ :=
  if a=.pop then none else top.bind bitSymbol

 def Action.secondWrite (a : Action) (current : Symbol Γ) : Symbol Γ :=
  match a with
  | .push b => bitSymbol b
  | _ => current

 theorem firstUpdate (a : Action) (w : Word) :
    stackHead w + (a.firstMove w.head?).displacement = stackHead (a.apply w) := by
  cases a <;> cases w <;>
    simp [stackHead,Action.firstMove,Action.apply,Motion.displacement]
  all_goals omega

 theorem secondUpdate (a : Action) (w : Word) (i : ℤ) :
    (if i=stackHead (a.apply w) then
      a.secondWrite (if stackHead (a.apply w)=stackHead w then
        a.firstWrite w.head? else stackCells w (stackHead (a.apply w)))
    else if i=stackHead w then a.firstWrite w.head? else stackCells (Γ:=Γ) w i) =
    stackCells (a.apply w) i := by
  cases a with
  | keep =>
    simp only [Action.apply,Action.secondWrite,Action.firstWrite,reduceCtorEq,ite_false,ite_true]
    split_ifs with h
    · subst i
      exact (stackCells_head w).symm
    · rfl
  | pop =>
    cases w with
    | nil => simp [Action.apply,Action.secondWrite,Action.firstWrite]
    | cons b w =>
      simp only [Action.apply,List.tail_cons,Action.secondWrite,Action.firstWrite,ite_true]
      have hh : stackHead (b::w)=stackHead w-1 := by
        simp only [stackHead,List.length_cons]; omega
      have hn : stackHead w ≠ stackHead w-1 := by omega
      simp only [hh,stackCells_cons,ite_eq_right hn]
      by_cases hi : i=stackHead w
      · subst i
        simp only [ite_true]
      · rw [ite_eq_right hi]
        by_cases hj : i=stackHead w-1
        · subst i
          simp only [ite_true]
          exact (stackCells_below w _ (by omega)).symm
        · simp only [ite_eq_right hj]
  | push b =>
    simp only [Action.apply,Action.secondWrite,Action.firstWrite,reduceCtorEq,ite_false]
    rw [stackCells_cons]
    have hh : stackHead (b::w)=stackHead w-1 := by
      simp only [stackHead,List.length_cons]; omega
    rw [hh]
    split_ifs with h₁ h₂
    · rfl
    · subst i
      exact (stackCells_head w).symm
    · rfl

structure Machine (Q : Type) (k : ℕ) where
  start : Q
  output : Fin (k+1)
  transition : Q → (Fin (k+1) → Option Bool) → Option (Q × (Fin (k+1) → Action))

structure State (Q : Type) (k : ℕ) where
  control : Q
  tapes : Fin (k+1) → Word

variable {Q : Type} {k : ℕ}

 def Machine.step (M : Machine Q k) (s : State Q k) : Option (State Q k) :=
  (M.transition s.control (fun j => (s.tapes j).head?)).map fun d =>
    {control := d.1,tapes := fun j => (d.2 j).apply (s.tapes j)}

 def Machine.initial (M : Machine Q k) (w : Word) : State Q k where
  control := M.start
  tapes := fun j => if j=0 then w.reverse else []

 def Machine.run (M : Machine Q k) (w : Word) : ℕ → State Q k
  | 0 => M.initial w
  | n+1 => (M.step (M.run w n)).getD (M.run w n)

 def Machine.OutputsWithin (M : Machine Q k) (w out : Word) (T : ℕ) : Prop :=
  ∃ t ≤ T, M.step (M.run w t)=none ∧ (M.run w t).tapes M.output=out

 theorem Action.length_apply_le (a : Action) (w : Word) : (a.apply w).length ≤ w.length+1 := by
  cases a <;> cases w <;> simp [Action.apply]
  all_goals omega

 theorem Machine.length_run (M : Machine Q k) (w : Word) (t : ℕ) (j : Fin (k+1)) :
    ((M.run w t).tapes j).length ≤ w.length+t := by
  induction t with
  | zero =>
    dsimp [Machine.run,Machine.initial]
    split_ifs <;> simp
  | succ t ih =>
    simp only [Machine.run]
    unfold Machine.step
    cases h : M.transition (M.run w t).control (fun i => ((M.run w t).tapes i).head?) with
    | none => dsimp; omega
    | some d =>
      dsimp
      exact (Action.length_apply_le _ _).trans (by omega)

end Stack
end VariableWL.Computation

end OAI
