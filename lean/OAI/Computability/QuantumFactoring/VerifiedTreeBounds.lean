import Mathlib
import OAI.Computability.QuantumFactoring.TreeHistoryAccess
import OAI.Computability.QuantumFactoring.NodeVerifiedCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PhysicalNode
abbrev resultBound (n : ℕ) := n*n+n*n*(498*n+114)
lemma resultField_count (n : ℕ) (i : Fin n) : (resultField n i).net.count≤n := by
  have h:=resizeWord_count (n+1) n
  simpa only [resultField,count_comp,NodeStateCircuit.output,count_select,blockNet,count_vector,
    Nat.zero_add] using h
lemma sortedOutput_count (n : ℕ) : (sortedOutput n).net.count≤resultBound n := by
  have h₁:=tensorNetwork_count_le (resultField n) (resultField_count n)
  have h₂:=SortedWords.sortNet_count n n
  simp only [sortedOutput,count_comp]
  unfold resultBound
  omega
end PhysicalNode
namespace PhysicalTree
lemma nodeResult_count (n : ℕ) : (nodeResult n).net.count≤PhysicalNode.resultBound n := by
  have h:=PhysicalNode.sortedOutput_count n
  simpa only [nodeResult,count_comp,SplitMachine.currentNet,count_select,Nat.zero_add] using h
lemma resultFields_count (n : ℕ) (i : Fin n) : (resultFields n i).net.count≤PhysicalNode.resultBound n := by
  simpa only [resultFields,count_comp,tensorSelect,count_select,Nat.add_zero] using nodeResult_count n
end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
lemma previousNet_count (t : ℕ) : (M.previousNet t).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
lemma lastNodeNet_count (t : ℕ) : (M.lastNodeNet t).net.count=0 := by
  simp only [lastNodeNet,count_comp,count_select,Nat.add_zero]
lemma rowQuery_count (t : ℕ) : (M.rowQuery t).net.count=M.query.net.count := by
  simp only [rowQuery,count_comp,M.previousNet_count,currentNet,count_select,Nat.zero_add]
lemma rowFields_count (t : ℕ) (i : Fin n) :
    (M.rowFields t i).net.count≤PhysicalNode.resultBound n := by
  simpa only [rowFields,count_comp,M.lastNodeNet_count,Nat.zero_add] using
    PhysicalTree.resultFields_count n i
abbrev rowBound := M.query.net.count+97*n+25+
  factorVerifierBound n (M.query.net.count+PhysicalNode.resultBound n)
lemma rowVerifiedNet_count (t : ℕ) : (M.rowVerifiedNet t).net.count≤M.rowBound := by
  have h₁:=zeroWord_count (M.rowQuery t)
  have h₂:=factorVerifierOn_count (M.rowQuery t) (M.rowFields t)
    (c:=M.query.net.count+PhysicalNode.resultBound n) (by rw [M.rowQuery_count];omega)
    (by intro i;exact (M.rowFields_count t i).trans (Nat.le_add_left _ _))
  rw [M.rowQuery_count] at h₁
  simp only [rowVerifiedNet,count_bor]
  unfold rowBound
  omega
lemma verifiedNet_count (t : ℕ) : (M.verifiedNet t).net.count≤t*(M.rowBound+1)+1 := by
  induction t with
  | zero=>simp only [verifiedNet,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ t ih=>
    have h:=M.rowVerifiedNet_count t
    simp only [verifiedNet,count_band,count_comp,M.previousNet_count,Nat.zero_add]
    nlinarith
end NodeMachine
end ExactQuantumFactoring


end

end OAI
