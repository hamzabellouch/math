import Mathlib
import OAI.Computability.MinUncut.Graphs.DemandOrder
import OAI.Computability.MinUncut.Machines.ArenaMachineProgram
import OAI.Computability.MinUncut.Machines.CodeFiniteMachine
import OAI.Computability.MinUncut.Graphs.GraphWordCodec

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial MinUncutGames.Foundations.Complexity
open MinUncut.PathRealization
noncomputable section

def fullGraphMachine : FinTM2 :=
  MachineSequential.machine (codeMachine rawRenderer.code) GraphCodec.machine id .cons

lemma fullGraphMachine_finiteAlphabet (k : fullGraphMachine.K) :
    Finite (fullGraphMachine.Γ k) :=
  sequential_finiteAlphabet _ _ _ _ (codeMachine_finiteAlphabet _) GraphCodec.finiteAlphabet k

def renderTime : Polynomial ℕ := C 10*rawRenderer.bound+10

def packedInput {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) : List ℕ :=
  N::ds.length::k::packDemands ds

lemma rawRenderer_output {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) :
    renderRaw (packedInput ds k)=
      (N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::packDemands ds) := by
  rw [packedInput,renderRaw_encode,rawGraphWords,rawTable_pack]

lemma codec_length_le (n k : ℕ) (v : List Bool) (rest : List ℕ) :
    (MinUncutGames.BinaryEncoding.nameBits n++v++MinUncutGames.BinaryEncoding.nameBits k).length≤
      2*magnitude (n::(v.map Bool.toNat++2::k::rest)) := by
  have hf (a : ℕ) : (MinUncutGames.BinaryEncoding.nameBits a).length≤2*a+1 := by
    have h := trNat_length_le a
    rw [GraphCodec.trNat_bits,List.length_map] at h
    have hg (w : List Bool) : (MinUncutGames.BinaryEncoding.frame w).length=2*w.length+1 := by
      induction w with
      | nil => rfl
      | cons b w ih => simp only [MinUncutGames.BinaryEncoding.frame,List.length_cons,ih]; omega
    rw [MinUncutGames.BinaryEncoding.nameBits,hg]
    omega
  have hm (w : List Bool) : w.length+k+3≤ magnitude (w.map Bool.toNat++2::k::rest) := by
    induction w with
    | nil => simp only [List.map_nil,List.nil_append,magnitude_cons,List.length_nil]; omega
    | cons b w ih =>
      simp only [List.map_cons,List.cons_append,magnitude_cons,List.length_cons]
      omega
  have hn := hf n; have hk := hf k; have h := hm v
  simp only [List.length_append,magnitude_cons]
  omega

def fullGraphMachine_outputs {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k) :
    TM2OutputsInTime fullGraphMachine (trList (packedInput ds k))
      (some (listOutput ds k hk).bits) (renderTime.eval (magnitude (packedInput ds k))) := by
  apply Classical.choice
  obtain ⟨t,ht,hc⟩ := rawRenderer.run (packedInput ds k)
  rw [rawRenderer_output] at hc
  have h1 := hc.finiteMachine
  have h2 := GraphCodec.outputsInTime (N+ds.length*3) k (canonicalTable ds) (packDemands ds)
  have h2' : TM2OutputsInTime GraphCodec.machine
      ((trList ((N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::packDemands ds))).map id)
      (some (MinUncutGames.BinaryEncoding.nameBits (N+ds.length*3)++canonicalTable ds++MinUncutGames.BinaryEncoding.nameBits k))
      (2*bitsize ((N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::packDemands ds))+
        (MinUncutGames.BinaryEncoding.nameBits (N+ds.length*3)++canonicalTable ds++MinUncutGames.BinaryEncoding.nameBits k).length+2) := by
    erw [List.map_id]
    exact h2
  have h := MachineSequential.execute (codeMachine rawRenderer.code) GraphCodec.machine id Γ'.cons
    _ _ _ _ _ h1 h2'
  have hm := rawRenderer.size (packedInput ds k)
  rw [rawRenderer_output] at hm
  have hb := (bitsize_le_magnitude _).trans hm
  have hl := codec_length_le (N+ds.length*3) k (canonicalTable ds) (packDemands ds)
  rw [←listOutput_bits ds k hk] at h
  refine ⟨⟨h.toEvalsTo,le_trans h.steps_le_m ?_⟩⟩
  simp only [renderTime,eval_add,eval_mul,eval_C,eval_ofNat]
  have hb2 := bitsize_le_magnitude ((N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::packDemands ds))
  have hl2 := hl
  rw [←listOutput_bits ds k hk] at hl2
  change t + 1 + 2 * ((trList ((N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::packDemands ds))).length + 1) +
    (2*bitsize ((N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::packDemands ds))+(listOutput ds k hk).bits.length+2) ≤ _
  simp only [bitsize] at hb hb2 ⊢
  omega

end
end MinUncut.Costed.GraphRegisters

namespace MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec Polynomial
open MinUncutGames.Foundations.Complexity
noncomputable section

def universalWords (v : List ℕ) : List ℕ :=
  let z := prepareOutput (control v)
  let r := (outputStep^[z.headI] z.tail).drop 2
  (prefixStep^[r.headI] (0::r.tail)).tail

def universalWordsProgram : PolyProgram universalWords :=
  reversePrefixProgram.comp ((PolyProgram.drop 2).comp
    (outputLoopProgram.comp (prepareOutputProgram.comp controlProgram)))

lemma universalWords_spec {c v w B} (hr : Runs c v w B) (hl : w.length≤B) (base : Heap) :
    ∃h,universalWords (B::(initialState c v base).encode)=w++w.reverse++2::words h := by
  obtain ⟨t,ht,hc⟩ := hr
  obtain ⟨h,out,ho,he⟩ := CodeRun.interpreted hc base ht
  refine ⟨h,?_⟩
  have hh : control (B::(initialState c v base).encode)=B::(State.mk 2 0 out 0 h).encode := by
    simpa only [control,List.headI_cons,keepTick_iter] using congrArg (List.cons B) he
  simp only [universalWords,hh]
  have hp : prepareOutput (B::(State.mk 2 0 out 0 h).encode)=B::(OutputState.mk out h []).encode := rfl
  rw [hp]
  simp only [List.headI_cons,List.tail_cons]
  rw [ho.output_padded [] hl]
  simp only [List.append_nil,OutputState.encode,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.headI_cons,List.tail_cons]
  rw [reversePrefix_spec,List.reverse_reverse,List.append_assoc]

def universalGraphMachine : FinTM2 :=
  MachineSequential.machine (codeMachine universalWordsProgram.code) GraphCodec.machine id .cons

lemma universalGraphMachine_finiteAlphabet (k : universalGraphMachine.K) :
    Finite (universalGraphMachine.Γ k) :=
  sequential_finiteAlphabet _ _ _ _ (codeMachine_finiteAlphabet _) GraphCodec.finiteAlphabet k

def universalGraphTime : Polynomial ℕ := C 10*universalWordsProgram.bound+10

def graphPacked (c : Code) (v : List ℕ) (B : ℕ) : List ℕ := B::(initialState c v []).encode

def universalGraphMachine_outputs {c : Code} {v : List ℕ} {B n k : ℕ}
    {table : List Bool} {rest : List ℕ}
    (hc : Runs c v (n::(table.map Bool.toNat++2::k::rest)) B)
    (hl : (n::(table.map Bool.toNat++2::k::rest)).length≤B) :
    TM2OutputsInTime universalGraphMachine (trList (graphPacked c v B))
      (some (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k))
      (universalGraphTime.eval (magnitude (graphPacked c v B))) := by
  apply Classical.choice
  obtain ⟨h,he⟩ := universalWords_spec hc hl []
  let junk := rest++(n::(table.map Bool.toNat++2::k::rest)).reverse++2::words h
  have he' : universalWords (graphPacked c v B)=n::(table.map Bool.toNat++2::k::junk) := by
    simpa only [graphPacked,List.cons_append,List.append_assoc,junk] using he
  obtain ⟨t,ht,hr⟩ := universalWordsProgram.run (graphPacked c v B)
  rw [he'] at hr
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
  have hh := MachineSequential.execute (codeMachine universalWordsProgram.code) GraphCodec.machine id Γ'.cons
    _ _ _ _ _ h1 h2'
  have hm := universalWordsProgram.size (graphPacked c v B)
  rw [he'] at hm
  have hb := bitsize_le_magnitude (n::(table.map Bool.toNat++2::k::junk))
  have ho := GraphRegisters.codec_length_le n k table junk
  refine ⟨⟨hh.toEvalsTo,hh.steps_le_m.trans ?_⟩⟩
  change t+1+2*((trList (n::(table.map Bool.toNat++2::k::junk))).length+1)+
    (2*bitsize (n::(table.map Bool.toNat++2::k::junk))+
      (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k).length+2)≤_
  simp only [universalGraphTime,eval_add,eval_mul,eval_C,eval_ofNat]
  simp only [bitsize] at hb ⊢
  omega
end
end MinUncut.Costed.Arena

end OAI
