import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryPrefix

namespace OAI

/-! Exact prefix parsing and emission for the verifier wrapper. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

@[simp] theorem next_some (h : TM2ComputableInPolyTime ea eb f) (c : (machine h).Cfg) :
    next h (some c)=(machine h).step c := rfl

@[simp] theorem tapes_input (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) :
    tapes h s xs bs ts (.inr 0)=xs := rfl

@[simp] theorem tapes_saved (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) :
    tapes h s xs bs ts (.inr 1)=bs := rfl

@[simp] theorem tapes_temp (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) :
    tapes h s xs bs ts (.inr 2)=ts := rfl

@[simp] theorem tapes_source (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) (k : h.tm.K) :
    tapes h s xs bs ts (.inl k)=s k := rfl

@[simp] theorem update_input (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts ys : List Bool) :
    Function.update (tapes h s xs bs ts) (.inr 0) ys=tapes h s ys bs ts := by
  classical
  funext k
  cases k with
  | inl k => simp [tapes,MachineEmbedding.tapes]
  | inr k => fin_cases k <;> simp [tapes,MachineEmbedding.tapes,extraTapes]

@[simp] theorem update_saved (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts ys : List Bool) :
    Function.update (tapes h s xs bs ts) (.inr 1) ys=tapes h s xs ys ts := by
  classical
  funext k
  cases k with
  | inl k => simp [tapes,MachineEmbedding.tapes]
  | inr k => fin_cases k <;> simp [tapes,MachineEmbedding.tapes,extraTapes]

@[simp] theorem update_temp (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts ys : List Bool) :
    Function.update (tapes h s xs bs ts) (.inr 2) ys=tapes h s xs bs ys := by
  classical
  funext k
  cases k with
  | inl k => simp [tapes,MachineEmbedding.tapes]
  | inr k => fin_cases k <;> simp [tapes,MachineEmbedding.tapes,extraTapes]

theorem parse_cons (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (xs : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 0)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode (n+1)) xs) (unaryCode k) [])=
      some (configuration h (some (.inr 0)) h.tm.initialState (some true)
        (fun _ => []) (pairBits (unaryCode n) xs) (unaryCode (k+1)) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,
    pairBits,unaryCode,List.replicate_succ,quoteBits_cons]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem parse_zero (h : TM2ComputableInPolyTime ea eb f) (k : ℕ)
    (xs : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 0)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode 0) xs) (unaryCode k) [])=
      some (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode k) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,
    pairBits,unaryCode]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem parse_steps (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (xs : List Bool) (r : Option Bool) :
    (next h)^[n+1] (some (configuration h (some (.inr 0)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode n) xs) (unaryCode k) []))=
      some (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode (k+n)) []) := by
  induction n generalizing k r with
  | zero => simpa only [Nat.add_zero,Nat.zero_add,Function.iterate_one,next_some] using
      parse_zero h k xs r
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [next_some,parse_cons,ih]
    rw [show k+1+n = k+(n+1) by omega]

theorem emit_delimiter (h : TM2ComputableInPolyTime ea eb f) (n : ℕ)
    (ys : List Bool) :
    (machine h).step (configuration h (some (.inr 5)) h.tm.initialState none
      (fun _ => []) ys (unaryCode n) [])=
      some (configuration h (some (.inr 6)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode 0) ys) (unaryCode n) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,pairBits,unaryCode]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem emit_cons (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (ys : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 6)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode k) ys) (unaryCode (n+1)) [])=
      some (configuration h (some (.inr 6)) h.tm.initialState (some true)
        (fun _ => []) (pairBits (unaryCode (k+1)) ys) (unaryCode n) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,
    pairBits,unaryCode,List.replicate_succ,quoteBits_cons]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem emit_zero (h : TM2ComputableInPolyTime ea eb f) (k : ℕ)
    (ys : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 6)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode k) ys) (unaryCode 0) [])=
      some (configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode k) ys) [] []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,unaryCode]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem emit_steps (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (ys : List Bool) (r : Option Bool) :
    (next h)^[n+1] (some (configuration h (some (.inr 6)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode k) ys) (unaryCode n) []))=
      some (configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode (k+n)) ys) [] []) := by
  induction n generalizing k r with
  | zero => simpa only [Nat.add_zero,Nat.zero_add,Function.iterate_one,next_some] using
      emit_zero h k ys r
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [next_some,emit_cons,ih]
    rw [show k+1+n = k+(n+1) by omega]

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
