import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryPrefixTransfers

namespace OAI

/-! Polynomial time for retaining a unary size certificate around an arbitrary
Boolean-input/Boolean-output TM2 computation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

theorem initial_eq (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    initList (machine h) (pairBits (unaryCode b) xs)=
      configuration h (some (.inr 0)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) xs) [] [] := by
  classical
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl k => simp [machine,tapes,MachineEmbedding.tapes]
  | inr k =>
    fin_cases k
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
      rfl
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]

theorem final_eq (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    haltList (machine h) (pairBits (unaryCode b) ys)=
      configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) ys) [] [] := by
  classical
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl k => simp [machine,tapes,MachineEmbedding.tapes]
  | inr k =>
    fin_cases k
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
      rfl
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]

def parse_run (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 0)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) xs) [] [])
      (some (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode b) [])) (b+1) where
  steps := b+1
  evals_in_steps := by
    change (next h)^[b+1] _=_
    simpa only [unaryCode,List.replicate_zero,Nat.zero_add] using parse_steps h b 0 xs none
  steps_le_m := le_rfl

def delimiter_run (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 5)) h.tm.initialState none
        (fun _ => []) ys (unaryCode b) [])
      (some (configuration h (some (.inr 6)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode 0) ys) (unaryCode b) [])) 1 where
  steps := 1
  evals_in_steps := by
    change (next h)^[1] _=_
    simpa only [Function.iterate_one,next_some] using emit_delimiter h b ys
  steps_le_m := le_rfl

def emit_run (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 6)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode 0) ys) (unaryCode b) [])
      (some (configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) ys) [] [])) (b+1) where
  steps := b+1
  evals_in_steps := by
    change (next h)^[b+1] _=_
    simpa only [unaryCode,List.replicate_zero,Nat.zero_add] using emit_steps h b 0 ys none
  steps_le_m := le_rfl

def execution (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (x : α) :
    TM2OutputsInTime (machine h) (pairBits (unaryCode b) (ea x))
      (some (pairBits (unaryCode b) (eb (f x))))
      (h.time.eval (ea x).length+2*b+2*(ea x).length+2*(eb (f x)).length+7) := by
  let r₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (parse_run h b (ea x)) (input_reverse h b (ea x))
  let r₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁ (input_restore h b (ea x))
  let r₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₂ (source_execution h b x)
  let r₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₃ (output_reverse h b (eb (f x)))
  let r₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₄ (output_restore h b (eb (f x)))
  let r₆ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₅ (delimiter_run h b (eb (f x)))
  let r₇ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₆ (emit_run h b (eb (f x)))
  change StateTransition.EvalsToInTime (machine h).step
    (initList (machine h) (pairBits (unaryCode b) (ea x)))
    (some (haltList (machine h) (pairBits (unaryCode b) (eb (f x))))) _
  rw [initial_eq,final_eq]
  refine ⟨r₇.toEvalsTo,?_⟩
  have hr := r₇.steps_le_m
  exact hr.trans (by omega)

def time (h : TM2ComputableInPolyTime ea eb f) : Polynomial ℕ :=
  Polynomial.C (1+2*TM2Size.programPushes h.tm)*h.time+6*Polynomial.X+7

theorem execution_bound (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (x : α) :
    h.time.eval (ea x).length+2*b+2*(ea x).length+2*(eb (f x)).length+7 ≤
      (time h).eval (pairBits (unaryCode b) (ea x)).length := by
  have hl : (pairBits (unaryCode b) (ea x)).length=2*b+1+(ea x).length := by
    simp [pairBits,quoteBits_length,unaryCode]
  have hm := MachineComposition.natPolynomial_eval_mono h.time
    (show (ea x).length ≤ (pairBits (unaryCode b) (ea x)).length by omega)
  have ho := TM2Size.output_length h x
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  nlinarith

def computable (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInPolyTime (prodCode unaryCode ea) (prodCode unaryCode eb)
      (fun x : ℕ × α => (x.1,f x.2)) where
  tm := machine h
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time h
  outputsFun x := by
    have hr := execution h x.1 x.2
    have run : TM2OutputsInTime (machine h)
        (pairBits (unaryCode x.1) (ea x.2))
        (some (pairBits (unaryCode x.1) (eb (f x.2))))
        ((time h).eval (pairBits (unaryCode x.1) (ea x.2)).length) :=
      ⟨hr.toEvalsTo,hr.steps_le_m.trans (execution_bound h x.1 x.2)⟩
    convert run using 1
    congr 1
    · exact List.map_id _
    · congr 1
      exact List.map_id _

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
