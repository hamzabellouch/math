import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.InitialLoop

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits outcomeBits)
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryCoupledLoop.run BinaryBisection.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ)
local notation "xx" => pack distance loc F v lo M N precision total k
local notation "bb" => BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0
local notation "qq" => BinaryInitialQuery.ctx bb total
local notation "II" => PriceBisection.search (fun lam=>initialCount loc distance F v lam total) k
    (PriceBisection.iterations lo (8*(d:ℚ)*M) precision) (lo,8*(d:ℚ)*M)
lemma high_pack : high xx=BinaryRational.encode (8*(d:ℚ)*M) := by
  simp only [high,pack,BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.length_replicate,BinaryRational.decode_encode]
lemma far_pack : far xx=BinaryRational.encode (20*N*M) := by
  simp only [far,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.length_replicate,BinaryRational.decode_encode]
lemma ctx_pack : ctx xx=qq := by
  simp only [ctx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryInitialQuery.ctx]
lemma loInput_pack : loInput xx=pairBits (qq,BinaryRational.encode lo) := by
  unfold loInput
  rw [ctx_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma loCount_pack : loCount xx=(initialCount loc distance F v lo total).bits := by
  unfold loCount
  rw [loInput_pack,BinaryInitialQuery.count_pack]
lemma loHistory_pack : loHistory xx=historyBits (initialHistory loc distance F v lo total) := by
  unfold loHistory
  rw [loInput_pack,BinaryInitialQuery.history_pack]
lemma loFinish_pack : loFinish xx=outputBits (finish ∅ lo [] (initialHistory loc distance F v lo total)) := by
  unfold loFinish
  rw [loHistory_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [outputBits,finish,List.nil_append,setBits,BinaryLabel.orderedSort,Finset.sort_empty,labels,List.map_nil,encode]
lemma bracketInput_pack : bracketInput xx=BinaryBisection.pack precision qq k lo (8*(d:ℚ)*M) := by
  unfold bracketInput
  rw [ctx_pack,high_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryBisection.pack]
lemma bracket_pack : bracket xx=pairBits (BinaryRational.encode II.1,BinaryRational.encode II.2) := by
  unfold bracket
  rw [bracketInput_pack,BinaryInitialQuery.search_pack]
lemma prices_pack : lower xx=BinaryRational.encode II.1 ∧ upper xx=BinaryRational.encode II.2 := by
  simp only [lower,upper,bracket_pack,extractPrefix_pairBits,discardPrefix_pairBits,and_self]
lemma inputs_pack : lowerInput xx=pairBits (qq,BinaryRational.encode II.1) ∧
    upperInput xx=pairBits (qq,BinaryRational.encode II.2) := by
  obtain ⟨hl,hu⟩:=prices_pack distance loc F v lo M N precision total k
  simp only [lowerInput,upperInput,ctx_pack,hl,hu,and_self]
lemma counts_pack : lowerCount xx=(initialCount loc distance F v II.1 total).bits ∧
    upperCount xx=(initialCount loc distance F v II.2 total).bits := by
  obtain ⟨hl,hu⟩:=inputs_pack distance loc F v lo M N precision total k
  simp only [lowerCount,upperCount,hl,hu,BinaryInitialQuery.count_pack,and_self]
lemma histories_pack : lowerHistory xx=historyBits (initialHistory loc distance F v II.1 total) ∧
    upperHistory xx=historyBits (initialHistory loc distance F v II.2 total) := by
  obtain ⟨hl,hu⟩:=inputs_pack distance loc F v lo M N precision total k
  simp only [lowerHistory,upperHistory,hl,hu,BinaryInitialQuery.history_pack,and_self]
lemma finishes_pack : lowerFinish xx=outputBits (finish ∅ II.1 [] (initialHistory loc distance F v II.1 total)) ∧
    upperFinish xx=outputBits (finish ∅ II.2 [] (initialHistory loc distance F v II.2 total)) := by
  obtain ⟨hl,hu⟩:=prices_pack distance loc F v lo M N precision total k
  obtain ⟨hL,hU⟩:=histories_pack distance loc F v lo M N precision total k
  simp only [lowerFinish,upperFinish,hl,hu,hL,hU,outputBits,finish,List.nil_append,
    setBits,BinaryLabel.orderedSort,Finset.sort_empty,labels,List.map_nil,encode,and_self]
lemma initialState_pack : initialState xx=stateBits (initial II.1 II.2 (initialHistory loc distance F v II.2 total)
    (initialHistory loc distance F v II.1 total)) := by
  obtain ⟨hl,hu⟩:=prices_pack distance loc F v lo M N precision total k
  obtain ⟨hL,hU⟩:=histories_pack distance loc F v lo M N precision total k
  simp only [initialState,hl,hu,hL,hU,stateBits,CanonicalCoupledMerge.initial,BinaryCorrection.encode,
    setBits,BinaryLabel.orderedSort,Finset.sort_empty,labels,List.map_nil,historyBits,encode]
lemma loopInput_pack : loopInput xx=BinaryCoupledLoop.pack bb (20*N*M) precision k
    ⟨0,total,.inr (initial II.1 II.2 (initialHistory loc distance F v II.2 total) (initialHistory loc distance F v II.1 total))⟩ := by
  unfold loopInput initialOutcome
  rw [far_pack,initialState_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCoupledLoop.pack,outcomeBits,List.replicate_zero]
end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
