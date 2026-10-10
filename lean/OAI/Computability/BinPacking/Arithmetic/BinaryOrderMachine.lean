import OAI.Computability.BinPacking.Reductions.BinaryTokenMachine

namespace OAI

namespace BinPackingGap.BinaryOrderMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinPackingCompleteness.BinaryEncoding (bitsValue bitsValue_bits)

def updateOrder (prior : Ordering) (left right : Bool) : Ordering :=
  if left = right then prior else if left then .gt else .lt

def scanOrder (left right : List Bool) (prior : Ordering) : Ordering :=
  match left, right with
  | [], [] => prior
  | [], b :: bs => scanOrder [] bs (updateOrder prior false b)
  | a :: as, [] => scanOrder as [] (updateOrder prior a false)
  | a :: as, b :: bs => scanOrder as bs (updateOrder prior a b)
termination_by left.length + right.length
decreasing_by all_goals simp_wf <;> omega

def orderNat (left right : Nat) (prior : Ordering := .eq) : Ordering :=
  if left < right then .lt else if right < left then .gt else prior

@[simp] theorem orderNat_self (n : Nat) (prior : Ordering) :
    orderNat n n prior = prior := by simp [orderNat]

theorem orderNat_bit (a b : Nat) (left right : Bool) (prior : Ordering) :
    orderNat a b (updateOrder prior left right) =
      orderNat (Nat.bit left a) (Nat.bit right b) prior := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hb : Nat.bit left a < Nat.bit right b := by
      cases left <;> cases right <;> simp only [Nat.bit_false, Nat.bit_true] <;> omega
    simp [orderNat, hlt, hb]
  · subst b
    cases left <;> cases right <;> simp [orderNat, updateOrder, Nat.bit]
  · have hb : Nat.bit right b < Nat.bit left a := by
      cases left <;> cases right <;> simp only [Nat.bit_false, Nat.bit_true] <;> omega
    simp [orderNat, hgt, Nat.not_lt.mpr hgt.le, hb, Nat.not_lt.mpr hb.le]

theorem scanOrder_value (left right : List Bool) (prior : Ordering) :
    scanOrder left right prior = orderNat (bitsValue left) (bitsValue right) prior := by
  induction left generalizing right prior with
  | nil =>
    induction right generalizing prior with
    | nil => simp [scanOrder, bitsValue, orderNat]
    | cons head tail ih =>
      rw [scanOrder, ih]
      simpa only [bitsValue, Nat.bit_false, Nat.mul_zero] using
        orderNat_bit 0 (bitsValue tail) false head prior
  | cons head tail ih =>
    cases right with
    | nil =>
      rw [scanOrder, ih]
      simpa only [bitsValue, Nat.bit_false, Nat.mul_zero] using
        orderNat_bit (bitsValue tail) 0 head false prior
    | cons rightHead rightTail =>
      rw [scanOrder, ih]
      exact orderNat_bit (bitsValue tail) (bitsValue rightTail) head rightHead prior

@[simp] theorem scanOrder_bits (a b : Nat) (prior : Ordering) :
    scanOrder a.bits b.bits prior = orderNat a b prior := by
  rw [scanOrder_value, bitsValue_bits, bitsValue_bits]

@[simp] theorem orderNat_eq_lt (a b : Nat) : orderNat a b .eq = .lt ↔ a < b := by
  unfold orderNat
  split_ifs <;> simp_all

@[simp] theorem orderNat_eq_gt (a b : Nat) : orderNat a b .eq = .gt ↔ b < a := by
  unfold orderNat
  split_ifs <;> simp_all
  omega

@[simp] theorem orderNat_eq_eq (a b : Nat) : orderNat a b .eq = .eq ↔ a = b := by
  unfold orderNat
  split_ifs <;> simp_all <;> omega

section Program

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := ((σ × Ordering) × Option Bool) × Option Bool

def clean (ambient : σ) : State σ := (((ambient, .eq), none), none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => clean state.1.1.1) (exitAt exit)

def loop (left right : K) (again : Λ) (exits : Ordering → Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => ((state.1.1, head), state.2))
    (.pop right (fun state head => (state.1, head))
      (.branch (fun state => state.1.2.isNone && state.2.isNone)
        (.branch (fun state => decide (state.1.1.2 = .lt))
          (finish (exits .lt))
          (.branch (fun state => decide (state.1.1.2 = .gt))
            (finish (exits .gt)) (finish (exits .eq))))
        (.load (fun state =>
          (((state.1.1.1, updateOrder state.1.1.2
            (state.1.2.getD false) (state.2.getD false)), none), none))
          (.goto fun _ => again))))

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes = ⟨exit, clean state.1.1.1, tapes⟩ := by
  simp [finish, TM2.stepAux]

private theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k; simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

private theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (ambient : σ) (prior : Ordering)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨exits prior, clean ambient, tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  cases prior <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right, clean]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ)
    (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some again, (((ambient, updateOrder prior false head), none), none),
        tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ)
    (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some again, (((ambient, updateOrder prior head false), none), none),
        tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some again, (((ambient, updateOrder prior leftHead rightHead), none), none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

private theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (prior : Ordering)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨exits (scanOrder [] rightWord prior), clean ambient,
        tapesAt left right base [] []⟩ := by
  induction rightWord generalizing prior leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, scanOrder] using
      step_empty left right distinct again exits program atLoop base ambient prior
        leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct again exits program atLoop]
    simpa only [scanOrder] using ih (updateOrder prior false head) none none

theorem compareTrace_prior (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨exits (scanOrder leftWord rightWord prior), clean ambient,
        tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord prior leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct again exits program atLoop base rightWord
        ambient prior leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some again, (((ambient, prior), leftRegister), rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct again exits program atLoop]
      simpa only [List.length_nil, Nat.max_zero, scanOrder] using
        ih [] (updateOrder prior head false) none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some again, (((ambient, prior), leftRegister), rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct again exits program atLoop]
      simpa only [scanOrder] using
        ih rightTail (updateOrder prior head rightHead) none none

theorem compareTrace (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some again, clean ambient, tapesAt left right base leftWord rightWord⟩) =
      some ⟨exits (orderNat (bitsValue leftWord) (bitsValue rightWord) .eq),
        clean ambient, tapesAt left right base [] []⟩ := by
  simpa only [clean, scanOrder_value] using
    compareTrace_prior left right distinct again exits program atLoop base leftWord rightWord
      ambient .eq none none

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some again, clean ambient, base⟩) =
      some ⟨exits (orderNat (bitsValue (base left)) (bitsValue (base right)) .eq),
        clean ambient, tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct again exits program atLoop base (base left) (base right) ambient

theorem drained_other (left right k : K) (notLeft : k ≠ left) (notRight : k ≠ right)
    (base : K → List Bool) : tapesAt left right base [] [] k = base k :=
  tapesAt_other left right k notLeft notRight base [] []

def compareInTime (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, clean ambient, base⟩
      (some ⟨exits (orderNat (bitsValue (base left)) (bitsValue (base right)) .eq),
        clean ambient, tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct again exits program atLoop base ambient
  steps_le_m := Nat.le_refl _

def compareNatInTime (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base left = a.bits) (rightWord : base right = b.bits) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, clean ambient, base⟩
      (some ⟨exits (orderNat a b .eq), clean ambient, tapesAt left right base [] []⟩)
      (max a.size b.size + 1) := by
  simpa only [leftWord, rightWord, bitsValue_bits, Nat.size_eq_bits_len] using
    compareInTime left right distinct again exits program atLoop base ambient

end Program

section Preserving

variable {K Λ σ : Type} [DecidableEq K]

inductive PreserveLabel
  | leftOut | leftBack | rightOut | rightBack | compare
  deriving DecidableEq

protected abbrev PreserveLabel.enumList : List PreserveLabel := [.leftOut, .leftBack, .rightOut,
  .rightBack, .compare]

protected theorem PreserveLabel.enumList_getElem?_ctorIdx_eq (x : PreserveLabel) :
    PreserveLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem PreserveLabel.enumList_nodup : PreserveLabel.enumList.Nodup := by decide

instance : Fintype PreserveLabel where
  elems := ⟨PreserveLabel.enumList, PreserveLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

def preservingInstruction (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ) : PreserveLabel → TM2.Stmt (Alphabet K) Λ (State σ)
  | .leftOut => loopAt (slots 0) (slots 4) id false
      (labels .leftOut) (some (labels .leftBack))
  | .leftBack => MachineCopy.forkLoop (slots 4) (slots 0) (slots 2) false
      (labels .leftBack) (some (labels .rightOut))
  | .rightOut => loopAt (slots 1) (slots 4) id false
      (labels .rightOut) (some (labels .rightBack))
  | .rightBack => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .rightBack) (some (labels .compare))
  | .compare => loop (slots 2) (slots 3) (labels .compare) exits

def preservingSteps (leftLength rightLength : Nat) : Nat :=
  2 * (leftLength + 1) + 2 * (rightLength + 1) + max leftLength rightLength + 1

theorem preservingSteps_le (leftLength rightLength : Nat) :
    preservingSteps leftLength rightLength ≤ 3 * (leftLength + rightLength) + 5 := by
  unfold preservingSteps
  omega

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem preservingTrace (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = preservingInstruction slots labels exits label)
    (base : K → List Bool) (leftEmpty : base (slots 2) = [])
    (rightEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[
        preservingSteps (base (slots 0)).length (base (slots 1)).length]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨exits (orderNat (bitsValue (base (slots 0))) (bitsValue (base (slots 1))) .eq),
        clean ambient, base⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let afterLeft := Function.update base (slots 2) (base (slots 0))
  let afterBoth := Function.update afterLeft (slots 3) (base (slots 1))
  have leftRun : (MachineComposition.advance (TM2.step program))^[
      2 * ((base (slots 0)).length + 1)]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨some (labels .rightOut), clean ambient, afterLeft⟩ := by
    have run := MachineCopy.copyTrace (slots 0) (slots 2) (slots 4)
      (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
      (labels .leftOut) (labels .leftBack) (some (labels .rightOut)) program
      (atLabels .leftOut) (atLabels .leftBack) base scratchEmpty ((ambient, .eq), none) none
    simpa only [leftEmpty, List.append_nil, clean, afterLeft] using run
  have rightWord : afterLeft (slots 1) = base (slots 1) := by
    simp [afterLeft, hd 1 2 (by decide)]
  have rightCopyEmpty : afterLeft (slots 3) = [] := by
    simp [afterLeft, hd 3 2 (by decide), rightEmpty]
  have scratchStillEmpty : afterLeft (slots 4) = [] := by
    simp [afterLeft, hd 4 2 (by decide), scratchEmpty]
  have rightRun : (MachineComposition.advance (TM2.step program))^[
      2 * ((base (slots 1)).length + 1)]
      (some ⟨some (labels .rightOut), clean ambient, afterLeft⟩) =
      some ⟨some (labels .compare), clean ambient, afterBoth⟩ := by
    have run := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4)
      (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
      (labels .rightOut) (labels .rightBack) (some (labels .compare)) program
      (atLabels .rightOut) (atLabels .rightBack) afterLeft scratchStillEmpty
      ((ambient, .eq), none) none
    simpa only [rightWord, rightCopyEmpty, List.append_nil, clean, afterBoth] using run
  have leftCopied : afterBoth (slots 2) = base (slots 0) := by
    simp [afterBoth, afterLeft, hd 2 3 (by decide)]
  have rightCopied : afterBoth (slots 3) = base (slots 1) := by
    simp [afterBoth]
  have restored : tapesAt (slots 2) (slots 3) afterBoth [] [] = base := by
    funext k
    by_cases hl : k = slots 2
    · subst k
      simp [tapesAt, hd 2 3 (by decide), leftEmpty]
    · by_cases hr : k = slots 3
      · subst k
        simp [tapesAt, rightEmpty]
      · simp [tapesAt, afterBoth, afterLeft, hl, hr]
  have comparisonRun := compareTrace_fromTapes (slots 2) (slots 3)
    (hd 2 3 (by decide)) (labels .compare) exits program (atLabels .compare) afterBoth ambient
  rw [leftCopied, rightCopied, restored] at comparisonRun
  have combined := joinTrace (joinTrace leftRun rightRun) comparisonRun
  simpa only [preservingSteps, Nat.add_assoc] using combined

def preservingInTime (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = preservingInstruction slots labels exits label)
    (base : K → List Bool) (leftEmpty : base (slots 2) = [])
    (rightEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exits (orderNat (bitsValue (base (slots 0))) (bitsValue (base (slots 1))) .eq),
        clean ambient, base⟩)
      (preservingSteps (base (slots 0)).length (base (slots 1)).length) where
  steps := preservingSteps (base (slots 0)).length (base (slots 1)).length
  evals_in_steps := preservingTrace slots labels exits program atLabels base
    leftEmpty rightEmpty scratchEmpty ambient
  steps_le_m := Nat.le_refl _

def preservingNatInTime (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = preservingInstruction slots labels exits label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (scratchEmpty : base (slots 4) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exits (orderNat a b .eq), clean ambient, base⟩)
      (preservingSteps a.size b.size) := by
  simpa only [leftWord, rightWord, bitsValue_bits, Nat.size_eq_bits_len] using
    preservingInTime slots labels exits program atLabels base leftEmpty rightEmpty scratchEmpty ambient

end Preserving

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := State Unit
  initialState := clean ()
  m label := if label = 0 then
    loop false true 0 (fun order => some (match order with | .lt => 1 | .eq => 2 | .gt => 3))
    else .halt

theorem machine_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet machine := by
  intro tape
  change Finite Bool
  infer_instance

def preservingMachine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := PreserveLabel ⊕ Ordering
  main := .inl .leftOut
  σ := State Unit
  initialState := clean ()
  m label := match label with
    | .inl phase => preservingInstruction (Function.Embedding.refl (Fin 5))
        Sum.inl (fun order => some (.inr order)) phase
    | .inr _ => .halt

theorem preservingMachine_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet preservingMachine := by
  intro tape
  change Finite Bool
  infer_instance

end BinPackingGap.BinaryOrderMachine

end OAI
