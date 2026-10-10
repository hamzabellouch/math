import Mathlib
import OAI.Computability.MinUncut.Encoding.PortTableEncoding
import OAI.Computability.MinUncut.Search.UniformRational
import OAI.Computability.MinUncut.Machines.GraphCoreMachine
import OAI.Computability.MinUncut.Encoding.BitOutputBound

namespace OAI

section
noncomputable section
namespace MinUncut.Uniform
open MinUncut.Costed MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing Turing.ToPartrec _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial
open MinUncutGames MinUncutGames.Foundations.Complexity
open MinUncutGames.BinaryEncoding
attribute [local irreducible] MinUncut.Preprocess.selectedInner MinUncut.Preprocess.selectedOuter
attribute [local irreducible] frontend frontendMachine program output initializerCode

def framedFrontend : FinTM2 :=
  Framed.machine frontendMachine.tm frontendMachine.inputAlphabet frontendMachine.outputAlphabet

def fullMachine : FinTM2 :=
  MachineSequential.machine framedFrontend coreMachine frontendMachine.outputAlphabet false
lemma full_finite (k : fullMachine.K) : Finite (fullMachine.Γ k) :=
  sequential_finiteAlphabet _ _ _ _
    (Framed.finiteAlphabet _ _ _ frontend_finite) core_finite k

def frontSize : Polynomial ℕ :=
  X+C (Runtime.programPushBound frontendMachine.tm)*frontendMachine.time
lemma frontSize_bound (F : BinaryFormula.Formula) :
    (MinUncutGames.Foundations.Complexity.formulaBits (frontend F).val).length≤
      frontSize.eval (formulaBits F).length :=
  Runtime.encodedOutputLength frontendMachine F

def fullTime (K : ℕ) : Polynomial ℕ :=
  frontendMachine.time+C (4*(nameBits K).length+3)+C 2*frontSize+(coreTime K).comp frontSize

def full_outputs (K : ℕ) (F : BinaryFormula.Formula) :
    TM2OutputsInTime fullMachine
      ((inputBits (K,F)).map frontendMachine.inputAlphabet.symm)
      (some (output K F).bits) ((fullTime K).eval (formulaBits F).length) := by
  let v:=formulaBits F
  let w:=MinUncutGames.Foundations.Complexity.formulaBits (frontend F).val
  let mid:=(nameBits K++w).map frontendMachine.outputAlphabet.symm
  let h1:=Framed.execute frontendMachine.tm frontendMachine.inputAlphabet frontendMachine.outputAlphabet
    K v w _ (frontendMachine.outputsFun F)
  have handoff:mid.map frontendMachine.outputAlphabet=nameBits K++w:=by
    simp only [mid,List.map_map,Function.comp_def,Equiv.apply_symm_apply]
    exact List.map_id _
  let h2: TM2OutputsInTime coreMachine (mid.map frontendMachine.outputAlphabet)
      (some (output K F).bits) ((coreTime K).eval w.length):=by
    erw [handoff]
    exact core_outputs K F
  let hh:=MachineSequential.execute framedFrontend coreMachine frontendMachine.outputAlphabet false
    _ _ _ _ _ h1 h2
  have hs:=frontSize_bound F
  have hc:=evalNat_mono (coreTime K) hs
  refine ⟨hh.toEvalsTo,hh.steps_le_m.trans ?_⟩
  change frontendMachine.time.eval v.length+2*(nameBits K).length+1+
    2*(mid.length+1)+(coreTime K).eval w.length≤(fullTime K).eval v.length
  simp only [mid,List.length_map,List.length_append,fullTime,eval_add,eval_C,eval_mul,eval_comp]
  dsimp only [v,w] at *
  omega

def computation : TM2Computable inputBits Output.bits (fun p=>output p.1 p.2) where
  tm := fullMachine
  inputAlphabet := frontendMachine.inputAlphabet
  outputAlphabet := Equiv.refl Bool
  outputsFun p := by
    change TM2Outputs fullMachine
      ((inputBits (p.1,p.2)).map frontendMachine.inputAlphabet.symm)
      (some ((output p.1 p.2).bits.map id))
    erw [List.map_id]
    exact (full_outputs p.1 p.2).toEvalsTo

def outputSize (K : ℕ) : Polynomial ℕ :=
  C 2*(C (nameBits K).length+X+fullTime K*C (Runtime.programPushBound fullMachine))
lemma outputSize_bound (K : ℕ) (F : BinaryFormula.Formula) :
    (output K F).vertices+(output K F).bits.length≤
      (outputSize K).eval (formulaBits F).length := by
  have h:=graph_size_of_runtime fullMachine (output K F)
    ((inputBits (K,F)).map frontendMachine.inputAlphabet.symm)
    (output K F).bits ((fullTime K).eval (formulaBits F).length) rfl (full_outputs K F)
  erw [List.length_map] at h
  simpa only [inputBits,List.length_append,outputSize,
    eval_mul,eval_add,eval_C,eval_X] using h

def reduction : Reduction where
  reduce := output
  machine := computation
  finiteAlphabet := full_finite
  time := fullTime
  runtime K F := by
    change TM2OutputsInTime fullMachine
      ((inputBits (K,F)).map frontendMachine.inputAlphabet.symm)
      (some ((output K F).bits.map id)) ((fullTime K).eval (formulaBits F).length)
    erw [List.map_id]
    exact full_outputs K F
  size := outputSize
  output_size := outputSize_bound
  yes K _ F hf := output_yes K F hf
  no := output_no
end MinUncut.Uniform
namespace MinUncut

theorem main : Nonempty Reduction := ⟨Uniform.reduction⟩
end MinUncut

end
end

end OAI
