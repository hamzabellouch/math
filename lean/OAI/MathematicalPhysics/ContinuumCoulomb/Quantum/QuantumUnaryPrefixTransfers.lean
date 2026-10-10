import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryPrefixRun

namespace OAI

/-! The four word transfers surrounding the original verifier computation.
The saved unary prefix is untouched throughout these phases. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity
open MinUncutGames.Reduction.MachineTransfer

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

@[simp] theorem update_source (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) (k : h.tm.K)
    (ys : List (h.tm.Γ k)) :
    Function.update (tapes h s xs bs ts) (.inl k) ys=
      tapes h (Function.update s k ys) xs bs ts := by
  classical
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=k
    · subst j; simp [tapes,MachineEmbedding.tapes,Function.update]
    · simp [tapes,MachineEmbedding.tapes,Function.update,hj]
  | inr j => simp [tapes,MachineEmbedding.tapes,Function.update]

def input_reverse (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode b) [])
      (some (configuration h (some (.inr 2)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) xs.reverse)) (xs.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inr (0 : Fin 3) : Tape h)
    (.inr 2) (by simp) id id (.inr 1) (some (.inr 2)) (program h) rfl
    (tapes h (fun _ => []) xs (unaryCode b) []) h.tm.initialState none
  simp only [tapes_input,tapes_temp,tapesAt,update_input,update_temp,
    Function.comp_def,id_eq,List.map_id',List.append_nil] at hr
  exact hr

def input_restore (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 2)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) xs.reverse)
      (some (MachineEmbedding.configuration (some (Sum.inr (3 : Fin 7))) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (initList h.tm (xs.map h.inputAlphabet.invFun)))) (xs.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inr (2 : Fin 3) : Tape h)
    (.inl h.tm.k₀) (by simp) id h.inputAlphabet.invFun (.inr 2) (some (.inl h.tm.main))
    (program h) rfl (tapes h (fun _ => []) [] (unaryCode b) xs.reverse) h.tm.initialState none
  simp only [tapes_temp,tapes_source,tapesAt,update_temp,update_source,
    Function.comp_def,id_eq,List.reverse_reverse,List.append_nil,List.length_reverse] at hr
  have hs : Function.update (fun k => ([] : List (h.tm.Γ k))) h.tm.k₀
      (xs.map h.inputAlphabet.invFun) = (initList h.tm (xs.map h.inputAlphabet.invFun)).stk := by
    funext k
    by_cases hk : k=h.tm.k₀
    · subst k
      simp [initList]
    · simp [initList,Function.update,hk]
  rw [hs] at hr
  exact hr

def output_reverse (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (MachineEmbedding.configuration (some (Sum.inr (3 : Fin 7))) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (haltList h.tm (ys.map h.outputAlphabet.invFun)))
      (some (configuration h (some (.inr 4)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) ys.reverse)) (ys.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inl h.tm.k₁ : Tape h)
    (.inr 2) (by simp) h.outputAlphabet id (.inr 3) (some (.inr 4)) (program h) rfl
    (tapes h (haltList h.tm (ys.map h.outputAlphabet.invFun)).stk [] (unaryCode b) [])
    h.tm.initialState none
  have hs : Function.update (haltList h.tm (ys.map h.outputAlphabet.invFun)).stk h.tm.k₁ []=
      fun k => ([] : List (h.tm.Γ k)) := by
    funext k
    by_cases hk : k=h.tm.k₁
    · subst k
      simp
    · simp [haltList,Function.update,hk]
  have ht : (haltList h.tm (ys.map h.outputAlphabet.invFun)).stk h.tm.k₁ =
      ys.map h.outputAlphabet.invFun := by simp [haltList]
  simp only [tapes_source,tapes_temp,tapesAt,update_source,update_temp,ht,hs,
    List.length_map,Function.comp_def,id_eq,List.map_reverse,List.map_map,
    List.append_nil] at hr
  have he : (fun x => h.outputAlphabet (h.outputAlphabet.invFun x)) = id :=
    funext h.outputAlphabet.right_inv
  rw [he,List.map_id] at hr
  exact hr

def output_restore (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 4)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) ys.reverse)
      (some (configuration h (some (.inr 5)) h.tm.initialState none
        (fun _ => []) ys (unaryCode b) [])) (ys.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inr (2 : Fin 3) : Tape h)
    (.inr 0) (by simp) id id (.inr 4) (some (.inr 5)) (program h) rfl
    (tapes h (fun _ => []) [] (unaryCode b) ys.reverse) h.tm.initialState none
  simp only [tapes_input,tapes_temp,tapesAt,update_input,update_temp,
    Function.comp_def,id_eq,List.map_id',List.append_nil,List.length_reverse,
    List.reverse_reverse] at hr
  exact hr

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
