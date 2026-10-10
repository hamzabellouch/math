import OAI.Computability.PerfectCompleteness.Machines.PayloadCellsMachine

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PayloadRowsLoop

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append)
open PayloadCellsMachine (SymbolSpec)


variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 11 ↪ K
abbrev Alphabet (_ : K) := Bool

def rowMap : Fin 9 ↪ Fin 11 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)

def rowPorts (p : Ports K) : PayloadPresenceMachine.Ports K := rowMap.trans p

def frame (p : Ports K) (base : K → List Bool) (remaining index capacity : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base (p 1) (encodeWord index))
    (p 9) (encodeWord remaining)) (p 10) (encodeWord capacity)

@[simp] theorem frame_index (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p base m i c (p 1) = encodeWord i := by simp [frame, p.injective.eq_iff]

@[simp] theorem frame_remaining (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p base m i c (p 9) = encodeWord m := by simp [frame, p.injective.eq_iff]

@[simp] theorem frame_capacity (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p base m i c (p 10) = encodeWord c := by simp [frame]

private theorem ext_ports (p : Ports K) {f g : K → List Bool}
    (atPorts : ∀ j, f (p j) = g (p j))
    (outside : ∀ k, (∀ j, k ≠ p j) → f k = g k) : f = g := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    exact atPorts j
  · exact outside k (fun j h => hk ⟨j, h.symm⟩)

theorem update_remaining (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 9) (encodeWord r) = frame p base r i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, p.injective.eq_iff]
  · intro k hk
    simp [frame, hk]

theorem update_index (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 1) (encodeWord r) = frame p base m r c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, p.injective.eq_iff]
  · intro k hk
    simp [frame, hk]

theorem update_capacity (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 10) (encodeWord r) = frame p base m i r := by
  simp [frame]

theorem frame_emitted (p : Ports K) (base : K → List Bool) (m i c : Nat) (tokens : List Token) :
    emitted (p 7) (p 8) (frame p base m i c) tokens =
      frame p (emitted (p 7) (p 8) base tokens) m i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, emitted, p.injective.eq_iff]
  · intro k hk
    simp [frame, emitted, hk]

theorem frame_ready (p : Ports K) (base : K → List Bool) (q m i c : Nat)
    (ready : PayloadPresenceMachine.Ready (rowPorts p) base q 0) :
    PayloadPresenceMachine.Ready (rowPorts p) (frame p base m i c) q i := by
  constructor
  · have rowPort : rowPorts p 0 = p 0 := by
      change p (rowMap 0) = p 0
      rw [rowMap.eq_1]
      rfl
    have boundWord : base (p 0) = encodeWord q := by
      simpa only [rowPort] using ready.boundWord
    change frame p base m i c (p 0) = encodeWord q
    simpa [frame, p.injective.eq_iff] using boundWord
  · exact frame_index p base m i c
  · intro j h₀ h₁ h₇ h₈
    have h1 : rowMap j ≠ (1 : Fin 11) := by
      intro h
      apply h₁
      exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
    have h9 : rowMap j ≠ (9 : Fin 11) := by
      intro h
      have hv := congrArg (fun x : Fin 11 => x.val) h
      change j.val = 9 at hv
      omega
    have h10 : rowMap j ≠ (10 : Fin 11) := by
      intro h
      have hv := congrArg (fun x : Fin 11 => x.val) h
      change j.val = 10 at hv
      omega
    simpa only [rowPorts, Function.Embedding.trans_apply, frame,
      Function.update_of_ne (p.injective.ne h10), Function.update_of_ne (p.injective.ne h9),
      Function.update_of_ne (p.injective.ne h1)] using ready.empty j h₀ h₁ h₇ h₈

inductive Label (symbols : Nat)
  | guard | next
  | row (entry : PayloadCellsMachine.Row.Label symbols)
  deriving DecidableEq, Fintype

def rowLabels (label : Label A ↪ Λ) : PayloadCellsMachine.Row.Label A ↪ Λ where
  toFun entry := label (.row entry)
  inj' := by intro i j h; exact Label.row.inj (label.injective h)

def statement (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (p 9) (label (.row (.visit 0))) exit
  | .next => .pop (p 10) (fun state _ => state)
      (.push (p 1) (fun _ => true) (.goto fun _ => label .guard))
  | .row entry => PayloadCellsMachine.Row.statement (rowPorts p) (rowLabels label)
      (some (label .next)) table entry

def Agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Λ) (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) : Prop :=
  ∀ entry, program (label entry) = statement p label exit table entry

theorem guardStep_zero (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .guard), clean ambient, frame p base 0 i c⟩ =
      some ⟨some exit, clean ambient, frame p base 0 i c⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, clean, encodeWord]

theorem guardStep_succ (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (m i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .guard), clean ambient, frame p base (m + 1) i c⟩ =
      some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i c⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, clean, encodeWord, List.replicate_succ]
  exact update_remaining p base (m + 1) i c m

theorem nextStep (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (m i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .next), clean ambient, frame p base m i (c + 1)⟩ =
      some ⟨some (label .guard), clean ambient, frame p base m (i + 1) c⟩ := by
  change some (TM2.stepAux (program (label .next)) _ _) = _
  rw [ha .next]
  simp only [statement, TM2.stepAux, frame_capacity, encodeWord, List.replicate_succ,
    List.cons_append, List.tail_cons]
  rw [Function.update_of_ne (p.injective.ne (by decide : (1 : Fin 11) ≠ 10))]
  change some (⟨some (label .guard), clean ambient,
    Function.update (Function.update (frame p base m i (c + 1)) (p 10) (encodeWord c))
      (p 1) (true :: frame p base m i (c + 1) (p 1))⟩ : TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
  rw [update_capacity, frame_index]
  rw [show true :: encodeWord i = encodeWord (i + 1) by simp [encodeWord, List.replicate_succ]]
  rw [update_index]

def tokens (table : Fin A → SymbolSpec) (q : Nat) : Nat → Nat → List Token
  | _, 0 => []
  | i, m + 1 => PayloadCellsMachine.Row.tokens table q i ++ tokens table q (i + 1) m

def steps (table : Fin A → SymbolSpec) (q : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | i, m + 1 => 1 + PayloadCellsMachine.Row.steps table q i + 1 + steps table q (i + 1) m

theorem trace (p : Ports K) (label : Label A ↪ Λ) (exit : Λ) (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (q i m c : Nat)
    (hbound : i + m ≤ q) (ready : PayloadPresenceMachine.Ready (rowPorts p) base q 0)
    (ambient : σ) :
    (advance (TM2.step program))^[steps table q i m]
      (some ⟨some (label .guard), clean ambient, frame p base m i (c + m)⟩) =
      some ⟨some exit, clean ambient,
        emitted (p 7) (p 8) (frame p base 0 (i + m) c) (tokens table q i m)⟩ := by
  induction m generalizing base i with
  | zero =>
    simpa only [steps, Function.iterate_one, advance_some, Nat.add_zero,
      tokens, ClashMachine.emitted_nil] using guardStep_zero p label exit table program ha base i c ambient
  | succ m ih =>
    have hi : i < q := by omega
    have hguard : (advance (TM2.step program))^[1]
        (some ⟨some (label .guard), clean ambient, frame p base (m + 1) i (c + (m + 1))⟩) =
        some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i (c + (m + 1))⟩ := by
      simpa only [Function.iterate_one, advance_some] using
        guardStep_succ p label exit table program ha base m i (c + (m + 1)) ambient
    have hrow := PayloadCellsMachine.Row.trace (rowPorts p) (rowLabels label)
      (some (label .next)) table program (fun entry => ha (.row entry))
      (frame p base m i (c + (m + 1))) q i hi (frame_ready p base q m i _ ready) ambient
    change (advance (TM2.step program))^[PayloadCellsMachine.Row.steps table q i]
      (some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i (c + (m + 1))⟩) =
      some ⟨some (label .next), clean ambient,
        emitted (p 7) (p 8) (frame p base m i (c + (m + 1)))
          (PayloadCellsMachine.Row.tokens table q i)⟩ at hrow
    rw [frame_emitted] at hrow
    let nextBase := emitted (p 7) (p 8) base (PayloadCellsMachine.Row.tokens table q i)
    have hnext : (advance (TM2.step program))^[1]
        (some ⟨some (label .next), clean ambient, frame p nextBase m i (c + (m + 1))⟩) =
        some ⟨some (label .guard), clean ambient, frame p nextBase m (i + 1) (c + m)⟩ := by
      simpa only [Function.iterate_one, advance_some, Nat.add_assoc] using
        nextStep p label exit table program ha nextBase m i (c + m) ambient
    have hn : PayloadPresenceMachine.Ready (rowPorts p) nextBase q 0 :=
      ready.emitted (PayloadCellsMachine.Row.tokens table q i)
    have htail := ih nextBase (i + 1) (by omega) hn
    have h := ClashMachine.chain (ClashMachine.chain (ClashMachine.chain hguard hrow) hnext) htail
    have hend : i + 1 + m = i + (m + 1) := by omega
    simpa only [steps, tokens, hend, nextBase, ← frame_emitted,
      emitted_append (p 7) (p 8) (p.injective.ne (by decide : (7 : Fin 11) ≠ 8))] using h

theorem steps_le (table : Fin A → SymbolSpec) (q i m : Nat) (hbound : i + m ≤ q) :
    steps table q i m ≤ m * (A * (120 * (q + 2) ^ 2 + 1) + 3) + 1 := by
  induction m generalizing i with
  | zero => simp [steps]
  | succ m ih =>
    have ht := ih (i + 1) (by omega)
    have hr := PayloadCellsMachine.Row.steps_le table q i (by omega)
    rw [steps, Nat.succ_mul]
    omega

theorem tokens_eq_forTokens (table : Fin A → SymbolSpec) (q i m : Nat) :
    tokens table q i m = forTokens m (fun j => PayloadCellsMachine.Row.tokens table q (i + j)) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    rw [tokens, forTokens_succ_first, Nat.add_zero, ih]
    apply congrArg (List.append (PayloadCellsMachine.Row.tokens table q i))
    apply forTokens_congr
    intro j _
    rw [show i + 1 + j = i + (j + 1) by omega]

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PayloadRowsLoop

end OAI
