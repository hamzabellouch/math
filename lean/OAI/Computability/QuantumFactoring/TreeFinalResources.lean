import Mathlib
import OAI.Computability.QuantumFactoring.TreeReadout

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma amplifiedProgram_length (n : ℕ) (hn : 0<n) :
    (amplifiedProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+8*(zeroNet n).net.count+12 :=
  amplificationProgram_length _ _ _ _ _

lemma amplifiedOutput_count (n : ℕ) (hn : 0<n) :
    (amplifiedOutput n hn).net.count=(quarterOutputNet n).net.count := by
  simp only [amplifiedOutput,count_comp,count_select,Nat.zero_add]

lemma paddedHistory_count (n : ℕ) : (paddedHistory n).net.count=0 := by
  simp only [paddedHistory,launchHistory,count_comp,count_select,Nat.zero_add]

lemma paddedOutputNet_count (n : ℕ) :
    (paddedOutputNet n).net.count=(rootFlat n (2*n^2)).net.count := by
  simp only [paddedOutputNet,count_comp,paddedHistory_count,Nat.zero_add]

lemma quarterOutputNet_count (n : ℕ) :
    (quarterOutputNet n).net.count≤(rootFlat n (2*n^2)).net.count+7*(n*n)+118 := by
  have h:=Completion.outputNet_count (paddedOutputNet n) 1 (n^11)
  rw [paddedOutputNet_count] at h
  change (Completion.outputNet (paddedOutputNet n) 1 (n^11)).net.count≤_
  omega

lemma factoringProgram_length (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+8*(zeroNet n).net.count+
      4*(quarterOutputNet n).net.count+2*(n*n)+12 := by
  have h₁:=readoutProgram_length (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl
  have h₂:=amplifiedProgram_length n hn
  have hc:=amplifiedOutput_count n hn
  change (readoutProgram (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl).length≤_
  omega

lemma readoutWidth_bound (n : ℕ) (hn : 0<n) :
    readoutWidth n hn≤quarterWidth n+1+(quarterFlag n hn).net.count+
      (zeroNet n).net.count+n*n+(quarterOutputNet n).net.count := by
  have hc:=amplifiedOutput_count n hn
  change quarterWidth n+1+max (quarterFlag n hn).net.count (zeroNet n).net.count+
    n*n+(amplifiedOutput n hn).net.count≤_
  omega

/-- Concrete reduction of the remaining whole-program resource obligation to
its literal preparation, accepted-event network, and root readout. These are
counts of actual gates/wires, not an assumed big-O charge for arithmetic. -/
theorem factoringProgram_resources (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+16*quarterWidth n+
      4*(rootFlat n (2*n^2)).net.count+30*(n*n)+492 ∧
    readoutWidth n hn≤3*quarterWidth n+(quarterFlag n hn).net.count+
      (rootFlat n (2*n^2)).net.count+8*(n*n)+120 := by
  have h₁:=factoringProgram_length n hn
  have h₂:=readoutWidth_bound n hn
  have h₃:=zeroNet_count n
  have h₄:=quarterOutputNet_count n
  constructor <;> omega

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
