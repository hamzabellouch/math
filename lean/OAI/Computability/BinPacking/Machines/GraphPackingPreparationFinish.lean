import OAI.Computability.BinPacking.Inventory.PackingConstantPool
import OAI.Computability.BinPacking.Machines.GraphPackingJobList

namespace OAI

noncomputable section

namespace BinPackingGap.PackingEndpointPower

open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {K : Type} [DecidableEq K]

def values (v power : Nat) : Fin 7 → Nat := ![v, 3, power, 0, 0, 0, 0]

def tallyRegister : BinaryToTallyMachine.Reg ↪ Fin 7 where
  toFun
    | .source => 0
    | .counter => 3
    | .one => 4
    | .temporary => 5
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def tallySlots (slots : (Fin 7 ⊕ Fin 6) ↪ K) :
    (BinaryToTallyMachine.Reg ⊕ Fin 6) ↪ K :=
  (Function.Embedding.sumMap tallyRegister (Function.Embedding.refl _)).trans slots

omit [DecidableEq K] in
@[simp] theorem tallySlots_reg (slots : (Fin 7 ⊕ Fin 6) ↪ K)
    (r : BinaryToTallyMachine.Reg) :
    tallySlots slots (.inl r) = slots (.inl (tallyRegister r)) := rfl

omit [DecidableEq K] in
@[simp] theorem tallySlots_scratch (slots : (Fin 7 ⊕ Fin 6) ↪ K) (j : Fin 6) :
    tallySlots slots (.inr j) = slots (.inr j) := rfl

def updateRegister : Fin 3 ↪ Fin 7 where
  toFun := ![1, 2, 5]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def updateSlots (slots : (Fin 7 ⊕ Fin 6) ↪ K) : (Fin 3 ⊕ Fin 6) ↪ K :=
  (Function.Embedding.sumMap updateRegister (Function.Embedding.refl _)).trans slots

omit [DecidableEq K] in
@[simp] theorem updateSlots_reg (slots : (Fin 7 ⊕ Fin 6) ↪ K) (r : Fin 3) :
    updateSlots slots (.inl r) = slots (.inl (updateRegister r)) := rfl

omit [DecidableEq K] in
@[simp] theorem updateSlots_scratch (slots : (Fin 7 ⊕ Fin 6) ↪ K) (j : Fin 6) :
    updateSlots slots (.inr j) = slots (.inr j) := rfl

def powerSlots (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (outside : ∀ q, slots q ≠ tally) : Fin 11 ↪ K where
  toFun := ![slots (.inl 1), slots (.inl 2), slots (.inl 5),
    slots (.inr 0), slots (.inr 1), slots (.inr 2), slots (.inr 3),
    slots (.inr 4), slots (.inr 5), tally, slots (.inl 6)]
  inj' := by
    intro i j h
    have hs (a b : Fin 7 ⊕ Fin 6) : slots a = slots b ↔ a = b := slots.injective.eq_iff
    have ht (a : Fin 7 ⊕ Fin 6) : tally ≠ slots a := (outside a).symm
    fin_cases i <;> fin_cases j <;> simp_all

structure Ready (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (base : K → List Bool) (v : Nat) : Prop where
  registers : ∀ r, base (slots (.inl r)) = (values v 0 r).bits
  scratch : ∀ j, base (slots (.inr j)) = []
  tallyEmpty : base tally = []

def code (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (outside : ∀ q, slots q ≠ tally) : Code (K := K) (S := State) :=
  .seq (PackingArithmeticProgram.code
    (BinaryToTallyMachine.code (tallySlots slots) tally))
    (.seq (PackingArithmeticProgram.code
      (PackingPowerProgram.code (powerSlots slots tally outside)))
      (PackingRegisterUpdate.code (updateSlots slots) .multiply))

def resultTapes (slots : (Fin 7 ⊕ Fin 6) ↪ K) (base : K → List Bool) (v : Nat) :
    K → List Bool := Function.update base (slots (.inl 2)) (3 ^ (v + 1)).bits

def timePolynomial : Polynomial Nat :=
  Polynomial.C 40 * (Polynomial.X + Polynomial.C 1) ^ 3 +
    Polynomial.C 100 * (Polynomial.X + Polynomial.C 4) ^ 5 +
    Polynomial.C 64 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 4) ^ 2 +
    Polynomial.C 2

@[simp] theorem timePolynomial_eval (v : Nat) :
    timePolynomial.eval v =
      40 * (v + 1) ^ 3 + 100 * (v + 4) ^ 5 + 64 * (2 * v + 4) ^ 2 + 2 := by
  simp [timePolynomial]

private theorem size_three : (3 : Nat).size = 2 := by decide

theorem tally_budget_le (v : Nat) :
    BinaryToTallyMachine.runtimeBound v ≤ 40 * (v + 1) ^ 3 := by
  have hs : v.size ≤ v := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsq := Nat.mul_le_mul (Nat.add_le_add_right hs 1) (Nat.add_le_add_right hs 1)
  have hm := Nat.mul_le_mul_left (40 * (v + 1)) hsq
  simpa only [BinaryToTallyMachine.runtimeBound, pow_succ, pow_two, pow_one,
    pow_zero, Nat.one_mul, Nat.mul_assoc] using hm

theorem power_budget (v : Nat) : PackingPowerProgram.budget 3 v = 100 * (v + 4) ^ 5 := by
  simp only [PackingPowerProgram.budget, BinaryPowerMachine.timePolynomial,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, size_three]
  congr 2
  omega

theorem multiply_budget_le (v : Nat) :
    64 * ((3 : Nat).size + (3 ^ v).size + 1) ^ 2 ≤ 64 * (2 * v + 4) ^ 2 := by
  have hp := BinaryArithmetic.size_pow_le 3 v
  rw [size_three] at hp ⊢
  have hw : 2 + (3 ^ v).size + 1 ≤ 2 * v + 4 := by omega
  simpa only [pow_two] using Nat.mul_le_mul_left 64 (Nat.mul_le_mul hw hw)

omit [DecidableEq K] in
private theorem register_frame_eq {Reg : Type} (slots : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (vals : Reg → Nat)
    (registers : ∀ r, base (slots (.inl r)) = (vals r).bits)
    (scratch : ∀ j, base (slots (.inr j)) = []) : registerTapes slots base vals = base := by
  funext k
  by_cases hk : ∃ q, slots q = k
  · obtain ⟨q, rfl⟩ := hk
    cases q with
    | inl r => simpa only [registerTapes_reg] using (registers r).symm
    | inr j => simpa only [registerTapes_scratch] using (scratch j).symm
  · exact registerTapes_other slots base vals k hk

theorem exec (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (outside : ∀ q, slots q ≠ tally) (base : K → List Bool) (v : Nat)
    (ready : Ready slots tally base v) (state : State) :
    ∃ steps ≤ timePolynomial.eval v,
      Exec (code slots tally outside) ⟨state, base⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes slots base v⟩ := by
  have hs (a b : Fin 7 ⊕ Fin 6) : slots a = slots b ↔ a = b := slots.injective.eq_iff
  have ht (a : Fin 7 ⊕ Fin 6) : tally ≠ slots a := (outside a).symm
  have tallyOutside : ∀ q, tallySlots slots q ≠ tally := by
    intro q
    cases q with
    | inl r => exact outside (.inl (tallyRegister r))
    | inr j => exact outside (.inr j)
  have tallyRegisters : ∀ r, base (tallySlots slots (.inl r)) =
      (BinaryToTallyMachine.initial v r).bits := by
    intro r
    cases r with
    | source => exact ready.registers 0
    | counter => exact ready.registers 3
    | one => exact ready.registers 4
    | temporary => exact ready.registers 5
  have tallyScratch : ∀ j, base (tallySlots slots (.inr j)) = [] := by
    intro j
    exact ready.scratch j
  let tallied := Function.update base tally (List.replicate v true)
  have convertRun : ∃ steps ≤ BinaryToTallyMachine.runtimeBound v,
      Exec (BinaryToTallyMachine.code (A := Unit) (tallySlots slots) tally)
        ⟨BinaryAddMachine.clean (), base⟩ steps
        ⟨BinaryAddMachine.clean (), tallied⟩ := by
    simpa only [ready.tallyEmpty, List.append_nil] using
      BinaryToTallyMachine.exec_from_tapes (tallySlots slots) tally tallyOutside base v
        tallyRegisters tallyScratch ()
  obtain ⟨ct, hc, converted⟩ := PackingArithmeticProgram.exec_in_time
    (BinaryToTallyMachine.code (tallySlots slots) tally) base tallied _ state convertRun
  have tallied_register (r : Fin 7) : tallied (slots (.inl r)) = (values v 0 r).bits := by
    simp only [tallied, Function.update_of_ne (outside (.inl r)), ready.registers]
  have tallied_scratch (j : Fin 6) : tallied (slots (.inr j)) = [] := by
    simp only [tallied, Function.update_of_ne (outside (.inr j)), ready.scratch]
  have powerSlot (j : Fin 11) : powerSlots slots tally outside j =
      ![slots (.inl 1), slots (.inl 2), slots (.inl 5),
        slots (.inr 0), slots (.inr 1), slots (.inr 2), slots (.inr 3),
        slots (.inr 4), slots (.inr 5), tally, slots (.inl 6)] j := rfl
  have powerReady : PackingPowerProgram.Ready (powerSlots slots tally outside) tallied 3 v := by
    constructor
    · exact tallied_register 1
    · exact tallied_register 2
    · change tallied tally = List.replicate v true
      simp only [tallied, Function.update_self]
    · intro j hj hj9
      rw [powerSlot]
      fin_cases j <;> simp_all [values]
  let powered := PackingPowerProgram.resultTapes (powerSlots slots tally outside) tallied 3 v
  obtain ⟨pt, hp, powerRun⟩ := PackingArithmeticProgram.exec_in_time
    (PackingPowerProgram.code (powerSlots slots tally outside)) tallied powered
    (PackingPowerProgram.budget 3 v) (.arithmetic (BinaryAddMachine.clean ()))
    (PackingPowerProgram.exec (powerSlots slots tally outside) tallied 3 v powerReady ())
  have powered_eq : powered = Function.update base (slots (.inl 2)) (3 ^ v).bits := by
    change Function.update
      (Function.update (Function.update base tally (List.replicate v true)) tally [])
      (slots (.inl 2)) (3 ^ v).bits = _
    rw [Function.update_idem, ← ready.tallyEmpty, Function.update_eq_self]
  have updateRegisters : ∀ r, powered (updateSlots slots (.inl r)) =
      (PackingRegisterUpdate.values 3 (3 ^ v) r).bits := by
    intro r
    rw [powered_eq]
    change Function.update base (slots (.inl 2)) (3 ^ v).bits
      (slots (.inl (![1, 2, 5] r))) = _
    fin_cases r <;> simp [hs, ready.registers, values, PackingRegisterUpdate.values]
  have updateScratch : ∀ j, powered (updateSlots slots (.inr j)) = [] := by
    intro j
    rw [powered_eq]
    simp [hs, ready.scratch]
  have updateFrame : registerTapes (updateSlots slots) powered
      (PackingRegisterUpdate.values 3 (3 ^ v)) = powered :=
    register_frame_eq (updateSlots slots) powered _ updateRegisters updateScratch
  have newValues : PackingRegisterUpdate.values 3
        (PackingRegisterUpdate.operation .multiply 3 (3 ^ v)) =
      Function.update (PackingRegisterUpdate.values 3 (3 ^ v)) 1 (3 * 3 ^ v) := by
    funext r
    fin_cases r <;> simp [PackingRegisterUpdate.values, PackingRegisterUpdate.operation]
  obtain ⟨mt, hm, multiplyRun⟩ := PackingRegisterUpdate.exec (updateSlots slots) .multiply
    powered 3 (3 ^ v) (.arithmetic (BinaryAddMachine.clean ()))
  rw [newValues, ← registerTapes_update, updateFrame] at multiplyRun
  have finalFrame : Function.update powered (updateSlots slots (.inl 1)) (3 * 3 ^ v).bits =
      resultTapes slots base v := by
    rw [powered_eq]
    change Function.update (Function.update base (slots (.inl 2)) (3 ^ v).bits)
      (slots (.inl 2)) (3 * 3 ^ v).bits = _
    simp only [Function.update_idem, resultTapes, Nat.pow_succ, Nat.mul_comm]
  rw [finalFrame] at multiplyRun
  refine ⟨ct + (pt + mt), ?_, Exec.seq converted (Exec.seq powerRun multiplyRun)⟩
  have hct := tally_budget_le v
  have hpt := power_budget v
  have hmt := multiply_budget_le v
  rw [timePolynomial_eval]
  omega

end BinPackingGap.PackingEndpointPower

namespace BinPackingGap.PackingVertexLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

abbrev VertexTape (num : δ → Expr α) (den : Expr α) (Other Extra : Type) :=
  PackingMachineLayout.Tape num den Other Extra

def body (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output : Extra) :
    Code (K := VertexTape num den Other Extra) (S := State) :=
  .seq (PackingArithmeticProgram.code
    (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
    (PackingRegisterUpdate.code
      (PackingVertexUpdate.updateSlots num den power three temp different) .multiply)

def code (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp)
    (output counter : Extra) : Code (K := VertexTape num den Other Extra) (S := State) :=
  PackingCountedProgram.loop (.inr counter)
    (body num den descriptors power three temp different output)

def bodyTimePolynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ) :
    Polynomial Nat :=
  PackingChunkMachine.timePolynomial num den descriptors + 1 +
    64 * (Polynomial.X + 3) ^ 2

omit [DecidableEq α] [DecidableEq δ] in
theorem bodyTimePolynomial_eval (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (width : Nat) :
    (bodyTimePolynomial num den descriptors).eval width =
      (PackingChunkMachine.timePolynomial num den descriptors).eval width + 1 +
        64 * (width + 3) ^ 2 := by
  simp [bodyTimePolynomial]

private theorem layout_external_update (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (external : Extra) (word : List Bool) :
    tapes num den (Function.update base (.inr external) word) input other =
      Function.update (tapes num den base input other) (.inr external) word := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

private theorem layout_output (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (output : Extra) (word : List Bool) :
    outputTapes (.inr output) (tapes num den base input other) word =
      tapes num den (outputTapes (.inr output) base word) input other := by
  unfold outputTapes
  rw [tapes_extra, layout_external_update]

private theorem layout_counter (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (counter : Extra) (n : Nat) :
    tapes num den (counterTapes (.inr counter) base n) input other =
      counterTapes (.inr counter) (tapes num den base input other) n := by
  exact layout_external_update num den base input other counter (List.replicate n true)

private theorem output_counter (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (output counter : Extra)
    (different : output ≠ counter) (word : List Bool) (n : Nat) :
    outputTapes (.inr output) (counterTapes (.inr counter) base n) word =
      counterTapes (.inr counter) (outputTapes (.inr output) base word) n := by
  funext k
  by_cases ho : k = .inr output
  · subst k
    simp [outputTapes, counterTapes, different]
  · by_cases hc : k = .inr counter
    · subst k
      simp [outputTapes, counterTapes, different, Ne.symm different]
    · simp [outputTapes, counterTapes, ho, hc]

theorem body_exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output : Extra)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hthree : other three = 3) (htemp : other temp = 0)
    (vertex width : Nat) (hwidth : ∀ a, (vertexInput input power vertex a).size ≤ width)
    (state : State) :
    ∃ steps ≤ (bodyTimePolynomial num den descriptors).eval width,
      Exec (body num den descriptors power three temp different output)
        ⟨state, tapes num den base (vertexInput input power vertex) other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den
            (outputTapes (.inr output) base
              (PackingChunkMachine.records num den
                (fun _ => vertexInput input power vertex) descriptors))
            (vertexInput input power (vertex + 1)) other⟩ := by
  let word := PackingChunkMachine.records num den
    (fun _ => vertexInput input power vertex) descriptors
  have chunk := PackingChunkMachine.exec num den (itemSlots num den) (.inr output)
    (fun d => itemSlots_outside num den d output) descriptors
    (tapes num den base (vertexInput input power vertex) other)
    (fun _ => vertexInput input power vertex) () width
    (fun d _ => item_shape num den base (vertexInput input power vertex) other d)
    (fun _ _ => hwidth)
  obtain ⟨emitSteps, emitBound, emitRun⟩ := PackingArithmeticProgram.exec_in_time
    (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors)
    _ _ _ state chunk
  rw [layout_output] at emitRun
  obtain ⟨updateSteps, updateBound, updateRun⟩ :=
    PackingVertexUpdate.exec num den power three temp different
      (outputTapes (.inr output) base word) (vertexInput input power vertex) other
      hthree htemp (.arithmetic (BinaryAddMachine.clean ()))
  rw [vertexInput_update] at updateRun
  refine ⟨emitSteps + updateSteps, ?_, Exec.seq emitRun updateRun⟩
  rw [bodyTimePolynomial_eval]
  have hp := hwidth power
  have sizeThree : (3 : Nat).size = 2 := by decide
  rw [sizeThree] at updateBound
  have square : (2 + (vertexInput input power vertex power).size + 1) ^ 2 ≤
      (width + 3) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have ub := updateBound.trans (Nat.mul_le_mul_left 64 square)
  omega

private theorem exec_bounded (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output counter : Extra)
    (outputCounter : output ≠ counter)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hthree : other three = 3) (htemp : other temp = 0)
    (start count width : Nat) (state : State)
    (hwidth : ∀ vertex, start ≤ vertex → vertex < start + count →
      ∀ a, (vertexInput input power vertex a).size ≤ width) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors).eval width + 1) + 1,
      Exec (code num den descriptors power three temp different output counter)
        ⟨state, counterTapes (.inr counter)
          (tapes num den base (vertexInput input power start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power start count))
            (vertexInput input power (start + count)) other) 0⟩ := by
  induction count generalizing start base state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more ((PackingCountedProgram.guard (.inr counter)).eval
          ⟨state, counterTapes (.inr counter)
            (tapes num den base (vertexInput input power start) other) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [code, PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        stream, PackingChunkMachine.outputTapes_nil, Nat.add_zero] using
        (Exec.loop_false (a := body num den descriptors power three temp different output) stop)
  | succ count ih =>
      let word := PackingChunkMachine.records num den
        (fun _ => vertexInput input power start) descriptors
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := body_exec num den descriptors
        power three temp different output (counterTapes (.inr counter) base count)
        input other hthree htemp start width (hwidth start (by omega) (by omega))
        (guardState (some true))
      rw [layout_counter, output_counter num den base output counter outputCounter,
        layout_counter] at bodyRun
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih
        (outputTapes (.inr output) base word) (start + 1)
        (.arithmetic (BinaryAddMachine.clean ()))
        (fun vertex lower upper => hwidth vertex (by omega) (by omega))
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter)
                (tapes num den base (vertexInput input power start) other) (count + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyRun' : Exec (body num den descriptors power three temp different output)
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter)
                (tapes num den base (vertexInput input power start) other) (count + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr counter)
              (tapes num den (outputTapes (.inr output) base word)
                (vertexInput input power (start + 1)) other) count⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun
        have combined := Exec.loop_true more bodyRun' tailRun
        simpa only [code, PackingCountedProgram.loop, word, stream,
          PackingChunkMachine.outputTapes_append, Nat.add_assoc, Nat.add_comm 1 count] using combined

theorem exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output counter : Extra)
    (outputCounter : output ≠ counter)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hthree : other three = 3) (htemp : other temp = 0)
    (start count inputWidth : Nat) (initial : ∀ a, (input a).size ≤ inputWidth)
    (state : State) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors).eval
        (aggregateWidth inputWidth start count) + 1) + 1,
      Exec (code num den descriptors power three temp different output counter)
        ⟨state, counterTapes (.inr counter)
          (tapes num den base (vertexInput input power start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power start count))
            (vertexInput input power (start + count)) other) 0⟩ := by
  exact exec_bounded num den descriptors power three temp different output counter
    outputCounter base input other hthree htemp start count
    (aggregateWidth inputWidth start count) state
    (fun vertex _ upper => vertexInput_size_le input power inputWidth start count vertex
      initial (Nat.le_of_lt upper))

def timePolynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ) :
    Polynomial Nat := Polynomial.X * (bodyTimePolynomial num den descriptors + 1) + 1

theorem exec_polynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output counter : Extra)
    (outputCounter : output ≠ counter)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hthree : other three = 3) (htemp : other temp = 0)
    (start count inputWidth : Nat) (initial : ∀ a, (input a).size ≤ inputWidth)
    (state : State) :
    ∃ steps ≤ (timePolynomial num den descriptors).eval
        (aggregateWidth inputWidth start count),
      Exec (code num den descriptors power three temp different output counter)
        ⟨state, counterTapes (.inr counter)
          (tapes num den base (vertexInput input power start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power start count))
            (vertexInput input power (start + count)) other) 0⟩ := by
  obtain ⟨steps, bound, run⟩ := exec num den descriptors power three temp different
    output counter outputCounter base input other hthree htemp start count inputWidth initial state
  refine ⟨steps, bound.trans ?_, run⟩
  have hc : count ≤ aggregateWidth inputWidth start count := by
    unfold aggregateWidth
    omega
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one] using
    Nat.add_le_add_right (Nat.mul_le_mul_right
      ((bodyTimePolynomial num den descriptors).eval
        (aggregateWidth inputWidth start count) + 1) hc) 1

end BinPackingGap.PackingVertexLoop

namespace BinPackingGap.GraphPackingProgram

section

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters

variable (fixed : InventoryData) (K : Nat)

abbrev Program := Code (K := Tape fixed K) (S := State)

def chain : List (Program fixed K) → Program fixed K
  | [] => .atom .done
  | c :: rest => .seq c (chain rest)

def regTape (r : Register fixed K) : Tape fixed K := slots fixed K (.inl r)

def otherSetup (o : PackingSetupExpression.Output) : Other fixed K :=
  .inl (PackingSetupMachine.output (parameters fixed K) o)

def tally (source : CountSource) (destination : Extra) : Program fixed K :=
  PackingArithmeticProgram.code
    (BinaryToTallyMachine.code (tallySlots fixed K source) (.inr destination))

def tallyToBinary (source : Extra) (destination : PackingSetupExpression.Input) :
    Program fixed K :=
  invoke arithmeticControl (BinaryAddMachine.clean ()) .scan
    (BinaryTallyMachine.instruction (.inr source) (regTape fixed K (input fixed K destination))
      (.inr .scanScratch) id none)

def power (source : CountSource) (destination : PackingItemExpression.Variable) :
    Program fixed K :=
  PackingArithmeticProgram.code (PackingPowerProgram.code (powerSlots fixed K source destination))

def setItem (destination : PackingItemExpression.Variable) (value : Nat) : Program fixed K :=
  PackingLayoutCommands.setInput (Numerator fixed) PackingItemExpression.denominator destination value

def setWork (destination : Work) (value : Nat) : Program fixed K :=
  PackingLayoutCommands.setOther (Numerator fixed) PackingItemExpression.denominator
    (.inr destination) value

def geometryOperands : Operands (Register fixed K) where
  destination := item fixed K .geometry
  left := work fixed K .geometryFactor
  right := item fixed K .totalPower
  left_ne_right := by
    change (Sum.inl (Sum.inr (Sum.inr Work.geometryFactor)) : Register fixed K) ≠
      Sum.inl (Sum.inl PackingItemExpression.Variable.totalPower)
    simp
  left_ne_destination := by
    change (Sum.inl (Sum.inr (Sum.inr Work.geometryFactor)) : Register fixed K) ≠
      Sum.inl (Sum.inl PackingItemExpression.Variable.geometry)
    simp
  right_ne_destination := by simp [item, PackingMachineLayout.inputs]

def geometry : Program fixed K :=
  chain fixed K [setWork fixed K .geometryFactor
      (160 * IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L),
    PackingAssignments.code (slots fixed K) [.mul (geometryOperands fixed K)]]

def header : Program fixed K :=
  chain fixed K [
    PackingAssignments.copy (slots fixed K) (work fixed K .header) (output fixed K .bins)
      (by simp [work, output, setup, PackingMachineLayout.others, PackingSetupMachine.output]),
    PackingArithmeticProgram.code
      (RegisterFrameEmission.code (regTape fixed K (work fixed K .header)) (.inr .reverseOutput))]

def prepare : Program fixed K :=
  chain fixed K [
    prepareGraph (graphSlots fixed K),
    tallyToBinary fixed K .vertices .n,
    tallyToBinary fixed K .edges .m,
    PackingArithmeticProgram.code (PackingFieldDecodeMachine.code (thresholdSlots fixed K)),
    PackingArithmeticProgram.code (PackingSetupMachine.code (parameters fixed K) (setupSlots fixed K)),
    tally fixed K (.input .n) .powerCounter,
    power fixed K (.output .three) .vertexPower,
    tally fixed K (.input .m) .powerCounter,
    power fixed K (.output .base) .totalPower,
    geometry fixed K,
    header fixed K]

def vertices : Program fixed K :=
  chain fixed K [setItem fixed K .labelPower 3,
    setItem fixed K .edgePower 1, setItem fixed K .repetitionOne 0,
    tally fixed K (.input .n) .vertexCounter,
    PackingVertexLoop.code (Numerator fixed) PackingItemExpression.denominator
      (PackingInventoryDescriptors.vertexDescriptors fixed) .labelPower
      (otherSetup fixed K .three) (.inr Work.temporary) (by simp [otherSetup])
      .reverseOutput .vertexCounter]

def endpoint (right : Bool) : Program fixed K :=
  chain fixed K [
    PackingArithmeticProgram.code (PackingFieldDecodeMachine.code (decoderSlots fixed K right)),
    PackingEndpointPower.code (endpointSlots fixed K right) (.inr .powerCounter)
      (endpoint_outside fixed K right .powerCounter)]

def incrementEdge : Program fixed K :=
  PackingRegisterUpdate.code
    (PackingVertexUpdate.updateSlots (Numerator fixed) PackingItemExpression.denominator .edgePower
      (otherSetup fixed K .base) (.inr Work.temporary) (by simp [otherSetup])) .multiply

def edgeBody : Program fixed K :=
  chain fixed K [
    .atom (.pop (.inr .endpoints) (fun state _ => state) .done),
    endpoint fixed K false,
    endpoint fixed K true,
    setItem fixed K .repetitionOne 1,
    tally fixed K (.output .repetitions) .repetitionCounter,
    PackingJobLoop.code (Numerator fixed) PackingItemExpression.denominator
      (PackingInventoryDescriptors.jobDescriptors fixed)
      .labelPower .repetitionOne (by decide)
      (.inr Work.leftPower) (.inr Work.rightPower)
      (otherSetup fixed K .one) (.inr Work.temporary) (by simp [otherSetup])
      .reverseOutput .repetitionCounter,
    incrementEdge fixed K,
    setWork fixed K .leftEndpoint 0,
    setWork fixed K .rightEndpoint 0,
    setWork fixed K .leftPower 0,
    setWork fixed K .rightPower 0,
    setItem fixed K .labelPower 0,
    setItem fixed K .repetitionOne 0]

def jobs : Program fixed K :=
  chain fixed K [setItem fixed K .edgePower 1,
    setItem fixed K .labelPower 0, setItem fixed K .repetitionOne 0,
    tally fixed K (.input .m) .edgeCounter,
    PackingCountedProgram.loop (.inr .edgeCounter) (edgeBody fixed K)]

def pool (stock : PackingSetupExpression.Output)
    (descriptor : PackingInventoryDescriptors.ItemDescriptor fixed) : Program fixed K :=
  chain fixed K [tally fixed K (.output stock) .poolCounter,
    PackingConstantPool.code (Numerator fixed) PackingItemExpression.denominator
      (PackingMachineLayout.itemSlots (Numerator fixed) PackingItemExpression.denominator)
      (.inr .reverseOutput) (.inr .poolCounter) [descriptor]]

def globalEdgeBody : Program fixed K :=
  chain fixed K [pool fixed K .edgeStock (.w, .globalEdge true),
    pool fixed K .edgeStock (.w, .globalEdge false), incrementEdge fixed K]

def globals : Program fixed K :=
  chain fixed K [setItem fixed K .labelPower 0,
    setItem fixed K .repetitionOne 0,
    setItem fixed K .edgePower 1,
    pool fixed K .upOne (.up, .globalUnit true),
    pool fixed K .upZero (.up, .globalUnit false),
    pool fixed K .umOne (.um, .globalUnit true),
    pool fixed K .umZero (.um, .globalUnit false),
    tally fixed K (.input .m) .edgeCounter,
    PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K)]

def flags : Program fixed K :=
  chain fixed K [setItem fixed K .edgePower 1,
    pool fixed K .treeFlags (.ft, .zero),
    pool fixed K .jobFlags (.fm, .zero), pool fixed K .jobFlags (.fg, .zero)]

def finish : Program fixed K :=
  chain fixed K [.atom (.push (.inr .reverseOutput) (fun _ => false) .done),
    PackingArithmeticProgram.code
      (.routine Unit inferInstance ()
        (fun _ => BinPackingGames.Reduction.MachineTransfer.loopAt
          (.inr Extra.reverseOutput) (.inr Extra.output) id false () none))]

def code : Program fixed K :=
  chain fixed K [prepare fixed K, vertices fixed K, jobs fixed K,
    globals fixed K, flags fixed K, finish fixed K]

def machine : FinTM2 :=
  (code fixed K).machine (.inr .input) (.inr .output) (.arithmetic (BinaryAddMachine.clean ()))

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (machine fixed K) :=
  Code.machine_finiteAlphabet (code fixed K) _ _ _

end

open FiniteTapeProgram

variable {fixed : InventoryData} {K : Nat}

inductive PhaseRuns : List (Program fixed K) →
    Data (GraphPackingRegisters.Tape fixed K) PackingMachineBlocks.State → Nat →
    Data (GraphPackingRegisters.Tape fixed K) PackingMachineBlocks.State → Prop
  | nil (state) : PhaseRuns [] state 0 state
  | cons {head tail before middle after n m}
      (first : Exec head before n middle) (rest : PhaseRuns tail middle m after) :
      PhaseRuns (head :: tail) before (n + m) after

namespace PhaseRuns

theorem single {code : Program fixed K} {before after n}
    (run : Exec code before n after) : PhaseRuns [code] before n after := by
  simpa only [Nat.add_zero] using PhaseRuns.cons run (PhaseRuns.nil after)

theorem append {first second : List (Program fixed K)} {before middle after n m}
    (left : PhaseRuns first before n middle) (right : PhaseRuns second middle m after) :
    PhaseRuns (first ++ second) before (n + m) after := by
  induction left with
  | nil => simpa only [List.nil_append, Nat.zero_add] using right
  | cons head tail ih =>
      simpa only [List.cons_append, Nat.add_assoc] using PhaseRuns.cons head (ih right)

theorem toExec {codes : List (Program fixed K)} {before after n}
    (runs : PhaseRuns codes before n after) :
    Exec (chain fixed K codes) before (n + 1) after := by
  induction runs with
  | nil state => exact Exec.atom .done state
  | cons first rest ih =>
      simpa only [chain, Nat.add_assoc] using Exec.seq first ih

end PhaseRuns

end BinPackingGap.GraphPackingProgram

namespace BinPackingGap.GraphPackingTapeBlocks

open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingRegisters PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

theorem slots_outside (destination : Extra) (q : Register fixed K ⊕ Fin 6) :
    slots fixed K q ≠ Sum.inr destination := by
  simp [slots, PackingMachineLayout.registers]

@[simp] theorem frame_extra (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (destination : Extra) :
    registerTapes (slots fixed K) base vals (.inr destination) = base (.inr destination) := by
  apply registerTapes_other
  rintro ⟨q, hq⟩
  exact slots_outside fixed K destination q hq

theorem tally_exec (source : CountSource) (destination : Extra)
    (base : Tape fixed K → List Bool) (vals : Register fixed K → Nat) (state : State)
    (counterZero : vals (work fixed K .counter) = 0)
    (oneZero : vals (work fixed K .one) = 0)
    (temporaryZero : vals (work fixed K .temporary) = 0) :
    ∃ steps ≤ BinaryToTallyMachine.runtimeBound (vals (countRegister fixed K source)) + 1,
      Exec (GraphPackingProgram.tally fixed K source destination)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K)
            (Function.update base (.inr destination)
              (List.replicate (vals (countRegister fixed K source)) true ++ base (.inr destination)))
            vals⟩ := by
  have registers : ∀ r,
      registerTapes (slots fixed K) base vals (tallySlots fixed K source (.inl r)) =
        (BinaryToTallyMachine.initial (vals (countRegister fixed K source)) r).bits := by
    intro r
    change registerTapes (slots fixed K) base vals
      (slots fixed K (.inl (match r with
        | .source => countRegister fixed K source
        | .counter => work fixed K .counter
        | .one => work fixed K .one
        | .temporary => work fixed K .temporary))) = _
    rw [registerTapes_reg]
    cases r <;> simp only [BinaryToTallyMachine.initial, counterZero, oneZero, temporaryZero]
  have scratch : ∀ j, registerTapes (slots fixed K) base vals
      (tallySlots fixed K source (.inr j)) = [] := by
    intro j
    simp [tallySlots]
  obtain ⟨t, ht, actual⟩ := BinaryToTallyMachine.exec_from_tapes
    (tallySlots fixed K source) (.inr destination)
    (tally_outside fixed K source destination) (registerTapes (slots fixed K) base vals)
    (vals (countRegister fixed K source)) registers scratch ()
  rw [frame_extra, ← external_update (slots fixed K) base vals (.inr destination)
    (slots_outside fixed K destination)] at actual
  exact PackingArithmeticProgram.exec_in_time
    (BinaryToTallyMachine.code (tallySlots fixed K source) (.inr destination))
    _ _ _ state ⟨t, ht, actual⟩

theorem power_exec (source : CountSource) (destination : PackingItemExpression.Variable)
    (base : Tape fixed K → List Bool) (vals : Register fixed K → Nat)
    (exponent : Nat) (state : State)
    (destinationZero : vals (item fixed K destination) = 0)
    (temporaryZero : vals (work fixed K .temporary) = 0)
    (reverseZero : vals (work fixed K .reverse) = 0)
    (tallyWord : base (.inr .powerCounter) = List.replicate exponent true) :
    ∃ steps ≤ PackingPowerProgram.budget (vals (countRegister fixed K source)) exponent + 1,
      Exec (GraphPackingProgram.power fixed K source destination)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (Function.update base (.inr .powerCounter) [])
            (Function.update vals (item fixed K destination)
              (vals (countRegister fixed K source) ^ exponent))⟩ := by
  have powerSlot (j : Fin 11) : powerSlots fixed K source destination j =
      ![slots fixed K (.inl (countRegister fixed K source)),
        slots fixed K (.inl (item fixed K destination)),
        slots fixed K (.inl (work fixed K .temporary)),
        slots fixed K (.inr 0), slots fixed K (.inr 1), slots fixed K (.inr 2),
        slots fixed K (.inr 3), slots fixed K (.inr 4), slots fixed K (.inr 5),
        .inr .powerCounter, slots fixed K (.inl (work fixed K .reverse))] j := rfl
  have ready : PackingPowerProgram.Ready (powerSlots fixed K source destination)
      (registerTapes (slots fixed K) base vals) (vals (countRegister fixed K source)) exponent := by
    constructor
    · simp [powerSlot]
    · simp [powerSlot, destinationZero]
    · simp [powerSlot, tallyWord]
    · intro j hj hj9
      fin_cases j <;> simp_all
  have after : PackingPowerProgram.resultTapes (powerSlots fixed K source destination)
      (registerTapes (slots fixed K) base vals) (vals (countRegister fixed K source)) exponent =
      registerTapes (slots fixed K) (Function.update base (.inr .powerCounter) [])
        (Function.update vals (item fixed K destination)
          (vals (countRegister fixed K source) ^ exponent)) := by
    change Function.update
      (Function.update (registerTapes (slots fixed K) base vals) (.inr .powerCounter) [])
      (slots fixed K (.inl (item fixed K destination)))
      (vals (countRegister fixed K source) ^ exponent).bits = _
    rw [← external_update (slots fixed K) base vals (.inr .powerCounter)
      (slots_outside fixed K .powerCounter), registerTapes_update]
  obtain ⟨t, ht, actual⟩ := PackingPowerProgram.exec (powerSlots fixed K source destination)
    (registerTapes (slots fixed K) base vals) (vals (countRegister fixed K source)) exponent ready ()
  rw [after] at actual
  exact PackingArithmeticProgram.exec_in_time
    (PackingPowerProgram.code (powerSlots fixed K source destination)) _ _ _ state ⟨t, ht, actual⟩

end BinPackingGap.GraphPackingTapeBlocks

namespace BinPackingGap.GraphPackingPreparation

section

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

def setupValues (x : GraphReductionInput) : Register fixed K → Nat :=
  PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
    (fun _ => 0) (setupOther fixed K x)

def firstPowerValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (setupValues fixed K x) (item fixed K .vertexPower) (3 ^ x.graph.n)

def secondPowerValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (firstPowerValues fixed K x) (item fixed K .totalPower)
    ((repetitions fixed K x + 1) ^ x.graph.edges.length)

def factorValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (secondPowerValues fixed K x) (work fixed K .geometryFactor)
    (geometryFactor fixed)

def finalValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (factorValues fixed K x) (item fixed K .geometry)
    (geometryFactor fixed * (repetitions fixed K x + 1) ^ x.graph.edges.length)

@[simp] theorem setupValues_item (x : GraphReductionInput) (v : PackingItemExpression.Variable) :
    setupValues fixed K x (item fixed K v) = 0 := rfl

@[simp] theorem setupValues_work (x : GraphReductionInput) (w : Work) :
    setupValues fixed K x (work fixed K w) = 0 := rfl

@[simp] theorem setupValues_input (x : GraphReductionInput) (i : PackingSetupExpression.Input) :
    setupValues fixed K x (input fixed K i) =
      PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k i := rfl

@[simp] theorem setupValues_output (x : GraphReductionInput) (o : PackingSetupExpression.Output) :
    setupValues fixed K x (output fixed K o) =
      PackingSetupExpression.outputValues (parameters fixed K)
        x.graph.n x.graph.edges.length x.k o := rfl

@[simp] theorem base_powerCounter (x : GraphReductionInput) :
    baseTapes fixed K x [] (.inr .powerCounter) = [] := rfl

theorem setup_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (PackingSetupMachine.timePolynomial (parameters fixed K)).eval (graphBits x).length + 1,
      Exec (PackingArithmeticProgram.code
        (PackingSetupMachine.code (parameters fixed K) (setupSlots fixed K)))
        ⟨state, parsedTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (baseTapes fixed K x) (setupValues fixed K x)⟩ := by
  let before := PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
    (fun _ => 0) (parsedOther fixed K x)
  have inputFrame : registerTapes (setupSlots fixed K) (parsedTapes fixed K x)
      (PackingSetupMachine.frame (parameters fixed K)
        (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0)) =
      parsedTapes fixed K x := by
    exact restrict (slots fixed K) (setup fixed K) (baseTapes fixed K x) before
  have outputFrame : registerTapes (setupSlots fixed K) (parsedTapes fixed K x)
      (PackingSetupMachine.frame (parameters fixed K)
        (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k)
        (PackingSetupExpression.outputValues (parameters fixed K)
          x.graph.n x.graph.edges.length x.k)) =
      registerTapes (slots fixed K) (baseTapes fixed K x) (setupValues fixed K x) := by
    apply replace (slots fixed K) (setup fixed K) (baseTapes fixed K x)
      before (setupValues fixed K x)
    · intro r; rfl
    · intro r outside
      rcases r with (v | (r | w)) | node
      · rfl
      · exact False.elim (outside ⟨r, rfl⟩)
      · rfl
      · rfl
  obtain ⟨t, ht, run⟩ := PackingSetupMachine.exec_graph (parameters fixed K)
    (setupSlots fixed K) (parsedTapes fixed K x) x ()
  rw [inputFrame, outputFrame] at run
  exact PackingArithmeticProgram.exec_in_time _ _ _ _ state ⟨t, ht, run⟩

def powerPhases : List (Program fixed K) :=
  [tally fixed K (.input .n) .powerCounter,
    power fixed K (.output .three) .vertexPower,
    tally fixed K (.input .m) .powerCounter,
    power fixed K (.output .base) .totalPower]

def powerBudget (x : GraphReductionInput) : Nat :=
  BinaryToTallyMachine.runtimeBound x.graph.n +
    PackingPowerProgram.budget 3 x.graph.n +
    BinaryToTallyMachine.runtimeBound x.graph.edges.length +
    PackingPowerProgram.budget (repetitions fixed K x + 1) x.graph.edges.length + 4

theorem powers_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ powerBudget fixed K x,
      PhaseRuns (powerPhases fixed K)
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (setupValues fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩ := by
  let base := baseTapes fixed K x
  let vals := setupValues fixed K x
  let counter (n : Nat) := Function.update base (.inr .powerCounter) (List.replicate n true)
  have clearCounter (n : Nat) : Function.update (counter n) (.inr .powerCounter) [] = base := by
    change Function.update
      (Function.update base (.inr .powerCounter) (List.replicate n true))
      (.inr .powerCounter) [] = base
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl
  obtain ⟨a, ha, arun⟩ := GraphPackingTapeBlocks.tally_exec fixed K (.input .n) .powerCounter
    base vals state rfl rfl rfl
  have arun' : Exec (tally fixed K (.input .n) .powerCounter)
      ⟨state, registerTapes (slots fixed K) base vals⟩ a
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.n) vals⟩ := by
    simpa only [vals, countRegister, setupValues_input, PackingSetupExpression.inputs,
      base, base_powerCounter, List.append_nil, counter] using arun
  obtain ⟨b, hb, brun⟩ := GraphPackingTapeBlocks.power_exec fixed K (.output .three) .vertexPower
    (counter x.graph.n) vals x.graph.n (.arithmetic (BinaryAddMachine.clean ())) rfl rfl rfl
    (by simp [counter])
  have brun' : Exec (power fixed K (.output .three) .vertexPower)
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.n) vals⟩ b
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        base (firstPowerValues fixed K x)⟩ := by
    simpa only [clearCounter, vals, countRegister, setupValues_output,
      PackingSetupExpression.outputValues, firstPowerValues] using brun
  have unchanged (r : Register fixed K) (hne : r ≠ item fixed K .vertexPower) :
      firstPowerValues fixed K x r = setupValues fixed K x r :=
    Function.update_of_ne hne _ _
  have workZero (w : Work) : firstPowerValues fixed K x (work fixed K w) = 0 := by
    rw [unchanged _ (by
      change (Sum.inl (Sum.inr (Sum.inr w)) : Register fixed K) ≠
        Sum.inl (Sum.inl .vertexPower)
      simp)]
    exact setupValues_work fixed K x w
  obtain ⟨c, hc, crun⟩ := GraphPackingTapeBlocks.tally_exec fixed K (.input .m) .powerCounter
    base (firstPowerValues fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    (workZero .counter) (workZero .one) (workZero .temporary)
  have inputM : firstPowerValues fixed K x (countRegister fixed K (.input .m)) =
      x.graph.edges.length := by
    rw [unchanged _ (by
      change (Sum.inl (Sum.inr (Sum.inl
        (PackingSetupMachine.input (parameters fixed K) .m))) : Register fixed K) ≠
          Sum.inl (Sum.inl .vertexPower)
      simp)]
    rfl
  have crun' : Exec (tally fixed K (.input .m) .powerCounter)
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        base (firstPowerValues fixed K x)⟩ c
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.edges.length) (firstPowerValues fixed K x)⟩ := by
    simpa only [inputM, base, base_powerCounter, List.append_nil, counter] using crun
  have totalEmpty : firstPowerValues fixed K x (item fixed K .totalPower) = 0 := by
    rw [unchanged _ (by
      intro h
      have equal := (item fixed K).injective h
      cases equal)]
    exact setupValues_item fixed K x .totalPower
  have baseValue : firstPowerValues fixed K x (countRegister fixed K (.output .base)) =
      repetitions fixed K x + 1 := by
    rw [unchanged _ (by
      change (Sum.inl (Sum.inr (Sum.inl
        (PackingSetupMachine.output (parameters fixed K) .base))) : Register fixed K) ≠
          Sum.inl (Sum.inl .vertexPower)
      simp)]
    rfl
  obtain ⟨d, hd, drun⟩ := GraphPackingTapeBlocks.power_exec fixed K (.output .base) .totalPower
    (counter x.graph.edges.length) (firstPowerValues fixed K x) x.graph.edges.length
    (.arithmetic (BinaryAddMachine.clean ())) totalEmpty (workZero .temporary) (workZero .reverse)
    (by simp [counter])
  have drun' : Exec (power fixed K (.output .base) .totalPower)
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.edges.length) (firstPowerValues fixed K x)⟩ d
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        base (secondPowerValues fixed K x)⟩ := by
    simpa only [clearCounter, baseValue, secondPowerValues] using drun
  refine ⟨a + (b + (c + d)), ?_, ?_⟩
  · rw [inputM] at hc
    rw [baseValue] at hd
    simp only [vals, countRegister, setupValues_input, PackingSetupExpression.inputs,
      setupValues_output, PackingSetupExpression.outputValues] at ha hb
    unfold powerBudget
    omega
  · exact PhaseRuns.cons arun' (PhaseRuns.cons brun'
      (PhaseRuns.cons crun' (PhaseRuns.single drun')))

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

variable (fixed : InventoryData) (K : Nat)

private theorem item_register (v : PackingItemExpression.Variable) :
    item fixed K v = (Sum.inl (Sum.inl v) : Register fixed K) := rfl

private theorem work_register (w : Work) :
    work fixed K w = (Sum.inl (Sum.inr (Sum.inr w)) : Register fixed K) := rfl

private theorem setupValues_width (x : GraphReductionInput) :
    ∀ r, (setupValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x := by
  apply PackingLayoutCommands.values_width
  · intro a; simp
  · intro a
    cases a with
    | inl r => exact GraphPackingWidths.setup_width fixed K x r
    | inr r => simp [setupOther]

private theorem firstPowerValues_width (x : GraphReductionInput) :
    ∀ r, (firstPowerValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _ (setupValues_width fixed K x) _ _
    (GraphPackingWidths.vertex_power_width fixed K x x.graph.n (by omega))

private theorem secondPowerValues_width (x : GraphReductionInput) :
    ∀ r, (secondPowerValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _ (firstPowerValues_width fixed K x) _ _
    (GraphPackingWidths.edge_power_width fixed K x x.graph.edges.length le_rfl)

private theorem factorValues_width (x : GraphReductionInput) :
    ∀ r, (factorValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _ (secondPowerValues_width fixed K x) _ _
    (GraphPackingWidths.preparedWork_width fixed K x .geometryFactor)

theorem finalValues_eq (x : GraphReductionInput) :
    finalValues fixed K x = PackingMachineLayout.values (Numerator fixed)
      PackingItemExpression.denominator (preparedInputs fixed K x) (preparedOther fixed K x) := by
  funext r
  rcases r with (a | (r | w)) | node
  · cases a <;> simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values, preparedInputs]
  · simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values, preparedOther, setupOther]
  · cases w <;> simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values, preparedOther, setupOther, preparedWork]
  · simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values]

private theorem finalValues_width (x : GraphReductionInput) :
    ∀ r, (finalValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x := by
  rw [finalValues_eq]
  exact PackingLayoutCommands.values_width _ _ _ _ _
    (GraphPackingWidths.preparedInputs_width fixed K x)
    (GraphPackingWidths.preparedOther_width fixed K x)

def geometryPolynomial : Polynomial Nat :=
  (runtimePolynomial (PackingAssignments.constantCommands (work fixed K .geometryFactor)
      (geometryFactor fixed)) +
    runtimePolynomial [.mul (geometryOperands fixed K)] + 5).comp
      (GraphPackingWidths.polynomial fixed K)

theorem geometry_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (geometryPolynomial fixed K).eval (graphBits x).length,
      Exec (geometry fixed K)
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩
        steps ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (baseTapes fixed K x) (finalValues fixed K x)⟩ := by
  obtain ⟨a, ha, arun⟩ := PackingAssignments.constant_exec (slots fixed K)
    (work fixed K .geometryFactor) (geometryFactor fixed) (baseTapes fixed K x)
    (secondPowerValues fixed K x) state (GraphPackingWidths.width fixed K x)
    (secondPowerValues_width fixed K x)
  have ready : Ready [.mul (geometryOperands fixed K)] (factorValues fixed K x) := by
    simp [Ready, commandReady, destination, geometryOperands, factorValues, secondPowerValues,
      firstPowerValues, setupValues, work_register, item_register, PackingMachineLayout.values]
  have mulResult : resultOf [.mul (geometryOperands fixed K)] (factorValues fixed K x) =
      finalValues fixed K x := by
    rw [resultOf_cons, resultOf_nil]
    simp [result, destination, value, geometryOperands,
      finalValues, factorValues, secondPowerValues, firstPowerValues,
      work_register, item_register]
  obtain ⟨b, hb, brun⟩ := PackingAssignments.exec (slots fixed K)
    [.mul (geometryOperands fixed K)] (baseTapes fixed K x) (factorValues fixed K x)
    ready (.arithmetic (BinaryAddMachine.clean ())) (GraphPackingWidths.width fixed K x)
    (factorValues_width fixed K x)
  rw [mulResult] at brun
  have first : Exec (setWork fixed K .geometryFactor (geometryFactor fixed))
      ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩ a
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        registerTapes (slots fixed K) (baseTapes fixed K x) (factorValues fixed K x)⟩ := arun
  refine ⟨a + b + 1, ?_, ?_⟩
  · simp only [geometryPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_ofNat]
    dsimp only [GraphPackingWidths.width] at ha hb
    omega
  · exact (PhaseRuns.cons first (PhaseRuns.single brun)).toExec

theorem headerDifferent : work fixed K .header ≠ output fixed K .bins := by
  simp [work, output, setup, PackingMachineLayout.others, PackingSetupMachine.output]

def headerPolynomial : Polynomial Nat :=
  (runtimePolynomial (PackingAssignments.copyCommands (work fixed K .header)
    (output fixed K .bins) (headerDifferent fixed K)) + Polynomial.X + 5).comp
      (GraphPackingWidths.polynomial fixed K)

theorem header_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (headerPolynomial fixed K).eval (graphBits x).length,
      Exec (header fixed K)
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (finalValues fixed K x)⟩
        steps ⟨.arithmetic (BinaryAddMachine.clean ()), preparedTapes fixed K x⟩ := by
  let vals := finalValues fixed K x
  let filled := Function.update vals (work fixed K .header) (binBound fixed K x)
  have bins : vals (output fixed K .bins) = binBound fixed K x := by
    rw [show vals = finalValues fixed K x from rfl, finalValues_eq]
    rfl
  have empty : vals (work fixed K .header) = 0 := by
    rw [show vals = finalValues fixed K x from rfl, finalValues_eq]
    rfl
  obtain ⟨a, ha, arun⟩ := PackingAssignments.copy_exec (slots fixed K)
    (work fixed K .header) (output fixed K .bins) (headerDifferent fixed K)
    (baseTapes fixed K x) vals state (GraphPackingWidths.width fixed K x)
    (finalValues_width fixed K x)
  rw [bins] at arun
  have cleared : Function.update filled (work fixed K .header) 0 = vals := by
    change Function.update
      (Function.update vals (work fixed K .header) (binBound fixed K x))
      (work fixed K .header) 0 = vals
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr empty.symm
  have baseUpdate : Function.update (baseTapes fixed K x) (.inr .reverseOutput)
      ((BinaryEncoding.natBits (binBound fixed K x)).reverse ++
        baseTapes fixed K x [] (.inr .reverseOutput)) =
      baseTapes fixed K x (BinaryEncoding.natBits (binBound fixed K x)).reverse := by
    funext t
    rcases t with r | e
    · simp [baseTapes]
    · cases e <;> simp [baseTapes]
  have native := RegisterFrameEmission.exec (slots fixed K) (baseTapes fixed K x)
    filled (work fixed K .header) (.inr .reverseOutput) (by intro i; simp [slots, PackingMachineLayout.registers]) ()
  have filledHeader : filled (work fixed K .header) = binBound fixed K x := by simp [filled]
  rw [filledHeader, cleared, baseUpdate] at native
  have emitted := PackingArithmeticProgram.exec _ _ _ _
    (.arithmetic (BinaryAddMachine.clean ())) native
  have finalFrame : registerTapes (slots fixed K)
      (baseTapes fixed K x (BinaryEncoding.natBits (binBound fixed K x)).reverse) vals =
      preparedTapes fixed K x := by
    rw [show vals = finalValues fixed K x from rfl, finalValues_eq]
    rfl
  rw [finalFrame] at emitted
  have binWidth : (binBound fixed K x).size ≤ GraphPackingWidths.width fixed K x :=
    GraphPackingWidths.setup_width fixed K x (PackingSetupMachine.output (parameters fixed K) .bins)
  refine ⟨a + (1 + ((binBound fixed K x).size + 1)) + 1, ?_, ?_⟩
  · simp only [headerPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    dsimp only [GraphPackingWidths.width] at ha binWidth
    omega
  · exact (PhaseRuns.cons arun (PhaseRuns.single emitted)).toExec

def finishPolynomial : Polynomial Nat := geometryPolynomial fixed K + headerPolynomial fixed K

theorem finish_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (finishPolynomial fixed K).eval (graphBits x).length,
      PhaseRuns [geometry fixed K, header fixed K]
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩
        steps ⟨.arithmetic (BinaryAddMachine.clean ()), preparedTapes fixed K x⟩ := by
  obtain ⟨a, ha, arun⟩ := geometry_exec fixed K x state
  obtain ⟨b, hb, brun⟩ := header_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  exact ⟨a + b, by simpa only [finishPolynomial, Polynomial.eval_add] using Nat.add_le_add ha hb,
    PhaseRuns.cons arun (PhaseRuns.single brun)⟩

end BinPackingGap.GraphPackingPreparation

end

end OAI
