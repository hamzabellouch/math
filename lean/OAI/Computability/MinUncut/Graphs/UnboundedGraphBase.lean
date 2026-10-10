import Mathlib
import OAI.Computability.MinUncut.Machines.UnboundedGraphMachine

namespace OAI

section
namespace MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec Polynomial
open MinUncutGames.Foundations.Complexity
noncomputable section

def unboundedGraphMachine_outputs_base {c : Code} {v : List ℕ} {B n k : ℕ}
    {table : List Bool} {rest : List ℕ} (base : Heap)
    (hc : Runs c v (n::(table.map Bool.toNat++2::k::rest)) B)
    (hl : (n::(table.map Bool.toNat++2::k::rest)).length≤B) :
    TM2OutputsInTime unboundedGraphMachine (trList ((initialState c v base).encode))
      (some (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k))
      (unboundedGraphTime.eval (magnitude (B::(initialState c v base).encode))) := by
  apply Classical.choice
  obtain ⟨h,hr,hm⟩ := unboundedWords_run hc hl base
  let junk := rest++(n::(table.map Bool.toNat++2::k::rest)).reverse++2::words h
  have he' : (n::(table.map Bool.toNat++2::k::rest))++
      (n::(table.map Bool.toNat++2::k::rest)).reverse++2::words h=
      n::(table.map Bool.toNat++2::k::junk) := by
    simp only [List.cons_append,List.append_assoc,junk]
  rw [he'] at hr hm
  obtain ⟨t,ht,hr⟩ := hr
  have h1 := hr.finiteMachine
  have h2 := GraphCodec.outputsInTime n k table junk
  have h2' : TM2OutputsInTime GraphCodec.machine
      ((trList (n::(table.map Bool.toNat++2::k::junk))).map id)
      (some (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k))
      (2*bitsize (n::(table.map Bool.toNat++2::k::junk))+
        (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k).length+2) := by
    have input_eq : @List.map (GraphCodec.machine.Γ GraphCodec.machine.k₀)
        (GraphCodec.machine.Γ GraphCodec.machine.k₀) id
        (trList (n::(table.map Bool.toNat++2::k::junk))) =
        trList (n::(table.map Bool.toNat++2::k::junk)) := List.map_id _
    simpa only [input_eq] using h2
  have hh := MachineSequential.execute (codeMachine unboundedWordsCode) GraphCodec.machine id Γ'.cons
    _ _ _ _ _ h1 h2'
  have hb := bitsize_le_magnitude (n::(table.map Bool.toNat++2::k::junk))
  have ho := GraphRegisters.codec_length_le n k table junk
  refine ⟨⟨hh.toEvalsTo,hh.steps_le_m.trans ?_⟩⟩
  change t+1+2*((trList (n::(table.map Bool.toNat++2::k::junk))).length+1)+
    (2*bitsize (n::(table.map Bool.toNat++2::k::junk))+
      (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k).length+2)≤_
  simp only [unboundedGraphTime,eval_add,eval_mul,eval_C,eval_ofNat]
  simp only [bitsize] at hb ⊢
  omega
end
end MinUncut.Costed.Arena

end

end OAI
