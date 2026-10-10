import Mathlib
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds
import OAI.Computability.QuantumFactoring.TreeFinalResources

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PhysicalTree

lemma flattenWords_count (n : ℕ) : (flattenWords n).net.count=0 := by
  have h:=wordBlocks_count (fun i : Fin n=>tensorSelect n n i)
    (c:=0) (fun _=>by simp only [tensorSelect,count_select,le_refl])
  change (flattenWords n).net.count≤n*n*0 at h
  omega

lemma rootFlat_count (n t : ℕ) :
    (rootFlat n t).net.count≤n*n+PhysicalNode.resultBound n := by
  cases t with
  | zero=>simp only [rootFlat,Completion.zeros_count];omega
  | succ t=>
    have h:=nodeResult_count n
    simp only [rootFlat,rootResult,count_comp,NodeMachine.firstNodeNet_count,
      flattenWords_count,Nat.zero_add,Nat.add_zero]
    omega

/-- All readout overhead is now bounded by an explicit polynomial expression;
the two remaining size estimates are preparation and same-history flagging. -/
theorem factoringProgram_resources_reduced (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+16*quarterWidth n+
      4*PhysicalNode.resultBound n+34*(n*n)+492 ∧
    readoutWidth n hn≤3*quarterWidth n+(quarterFlag n hn).net.count+
      PhysicalNode.resultBound n+9*(n*n)+120 := by
  have h₁:=factoringProgram_resources n hn
  have h₂:=rootFlat_count n (2*n^2)
  constructor <;> omega

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
