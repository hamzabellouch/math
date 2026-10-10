import Mathlib
import OAI.Computability.QuantumFactoring.FlatLookupCircuit
import OAI.Computability.QuantumFactoring.VerifiedTableOrder
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Every field is selected from its actual retained location. Dummy rows
are kept: the rectangular shape is a compile-time function only of n and t. -/
def fieldRows (t : ℕ) : List (BooleanNetwork (M.width t) n ×
    List (BooleanNetwork (M.width t) n)) :=
  (M.logNets t).map (fun r=>(r.1,List.ofFn (fun i : Fin n=>r.2.comp (tensorSelect n n i))))

lemma fieldRows_length (t : ℕ) : (M.fieldRows t).length=t := by
  simp only [fieldRows,List.length_map,M.logNets_length]

lemma fieldRows_values (x : Basis c) (t : ℕ) (h : Trace n t) :
    tableValues (M.fieldRows t) (M.encoded x t h)=M.dataLog x t h := by
  rw [←M.logNets_values x t h]
  simp only [fieldRows,tableValues,List.map_map,Function.comp_def,List.map_ofFn,
    eval_comp,tensorSelect_inverse,SortedWords.numbers,List.map_ofFn]

lemma fieldRows_counts (t : ℕ) : ∀ r∈M.fieldRows t,
    r.1.net.count ≤ M.query.net.count ∧ ∀ p∈r.2,p.net.count ≤ PhysicalNode.resultBound n := by
  intro r hr
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
  have hh:=M.logNets_counts t a ha
  refine ⟨hh.1,?_⟩
  intro p hp
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
  simpa only [count_comp,tensorSelect,count_select,Nat.add_zero] using hh.2

lemma fieldRows_table_length (t : ℕ) : (tableNets (M.fieldRows t)).length=t*n := by
  have h : ∀ a : BooleanNetwork (M.width t) n×BooleanNetwork (M.width t) (tensorWidth n n),
      (List.ofFn (fun i : Fin n => tableFactor a.1 (a.2.comp (tensorSelect n n i)))).length=n :=
    fun _=>List.length_ofFn
  simp only [tableNets,fieldRows,List.flatMap_map,Function.comp_def,List.map_ofFn,
    List.length_flatMap]
  simp only [h,List.map_const',List.sum_replicate,smul_eq_mul,M.logNets_length]

/-- The literal order network already available at any retained stage, before
adding its reversible phase-flag wrapper. -/
def retainedOrder (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) n :=
  tableOrder a m (M.fieldRows t)

lemma retainedOrder_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedOrder t a m).eval (M.encoded x t r))).toNat=orderOf u := by
  apply tableOrder_exact hn a m (M.fieldRows t) (M.encoded x t r)
  · rwa [M.fieldRows_values]
  · rwa [M.fieldRows_values]
  · exact hP0
  · exact hd
  · exact hdiv
  · exact ha
  · exact hm

lemma retainedOrder_count {b : ℕ} (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (ha : a.net.count ≤ b) (hm : m.net.count ≤ b)
    (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedOrder t a m).net.count ≤ tableOrderBound n (t*n) b := by
  have hh:=tableOrder_count a m (M.fieldRows t) ha hm (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  rwa [M.fieldRows_table_length] at hh

end NodeMachine
end ExactQuantumFactoring


end

end OAI
