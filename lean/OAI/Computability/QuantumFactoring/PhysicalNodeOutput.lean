import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalNodeCompletion
import OAI.Computability.QuantumFactoring.SortedEncoding
import OAI.Computability.QuantumFactoring.TensorList

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalNode

def resultField (n : ℕ) (i : Fin n) : BooleanNetwork (configWidth n (2*n)) n :=
  ((NodeStateCircuit.output (2*n) (n+1)).comp
    (blockNet (2*n+1) (n+1) ⟨i.val,by omega⟩)).comp (resizeWord (n+1) n)

def sortedOutput (n : ℕ) : BooleanNetwork (configWidth n (2*n)) (tensorWidth n n) :=
  (tensorNetwork (resultField n)).comp (SortedWords.sortNet n n)

def shrink (n : ℕ) (a : Basis (n+1)) : Basis n := (resizeWord (n+1) n).eval a

lemma resultField_pack (n : ℕ) (xs ys : List (Basis (n+1))) (b : Bool) (i : Fin n) :
    (resultField n i).eval (NodeStateCircuit.pack xs ys b)=
      shrink n (ys[i.val]?.getD (fun _=>false)) := by
  rw [resultField,eval_comp,eval_comp,NodeStateCircuit.output_pack,blockNet_eval,block_stackEncoding]
  rfl
lemma shrink_zero (n : ℕ) : shrink n (fun _=>false)=(fun _=>false) := by
  funext i
  simp only [shrink,resizeWord,eval_vector]
  rw [dite_eq_left (by omega)]
  rfl

lemma sortedOutput_pack (n : ℕ) (xs ys : List (Basis (n+1))) (b : Bool) (hlen : ys.length ≤ n) :
    (sortedOutput n).eval (NodeStateCircuit.pack xs ys b)=SortedWords.layout n n
      (SortedWords.sort (ys.map (shrink n)++List.replicate (n-ys.length) (fun _=>false))) := by
  rw [sortedOutput,eval_comp,tensorNetwork_eval]
  simp_rw [resultField_pack]
  rw [←SortedWords.layout_ofFn]
  rw [SortedWords.sortNet_eval _ _ _ List.length_ofFn,
    SortedWords.ofFn_map_getD_pad ys (fun _=>false) n hlen,shrink_zero]

lemma shrink_values {n : ℕ} (ys : List (Basis (n+1))) (hb : ∀ a∈ys,(bitsValue a).toNat<2^n) :
    SortedWords.numbers (ys.map (shrink n))=values ys := by
  simp only [SortedWords.numbers,values,List.map_map]
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply,shrink,resizeWord_value,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (hb a ha)]

/-- The actual retained node configuration admits an explicit polynomial
Boolean sorting/readout network. Its output is the LITERAL main-theorem
encoding, with exactly n fields, zero padding and multiplicities. -/
theorem complete_output {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (h : SplitMachine.Trace n (2*n))
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (sortedOutput n).eval
        ((machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h)=
          SortedWords.layout n n zs := by
  obtain ⟨ys,he,hpr,hprod,hlen⟩ := complete hn hN hb h hp
  have hyb : ∀ a∈ys,(bitsValue a).toNat<2^n := by
    intro a ha
    have hm : (bitsValue a).toNat∈values ys := List.mem_map.mpr ⟨a,ha,rfl⟩
    have hd : (bitsValue a).toNat∣N := by rw [←hprod];exact List.dvd_prod hm
    exact (Nat.le_of_dvd (by omega) hd).trans_lt hb
  have hv := shrink_values ys hyb
  refine ⟨SortedWords.sort (ys.map (shrink n)++List.replicate (n-ys.length) (fun _=>false)),?_,?_,?_⟩
  · simp only [SortedWords.sort_length,List.length_append,List.length_map,List.length_replicate]
    omega
  · have hc := SortedWords.sort_correct (N:=N) (r:=n) (ys.map (shrink n)) (by rw [hv];exact hpr)
      (by rw [hv];exact hprod) (by simp only [List.length_map];omega : (ys.map (shrink n)).length ≤ n)
    simpa only [List.length_map] using hc
  · rw [he,sortedOutput_pack _ _ _ _ hlen.le]

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
