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
open BooleanNetwork BitArithmetic OrderTrial

lemma natBasis_apply (w N : ℕ) (i : Fin w) : natBasis w N i=N.testBit i.val := by
  simp only [natBasis,BitVec.getLsbD_ofNat,decide_true,i.isLt,Bool.true_and]

/-- The sole nondeterministic-preparation branch bit precedes the retained N;
all remaining physical input coordinates are clean. -/
def shiftedInput (q n N : ℕ) : Basis q :=
  fun i=>if 1 ≤ i.val ∧ i.val < 1+n then N.testBit (i.val-1) else false

lemma packed_shifted {q m r n N : ℕ} (hn : 1+n≤q) :
    packed r (shiftedInput q n N) (fun _ : Fin m=>false)=shiftedInput (q+m+r) n N := by
  funext i
  simp only [packed,shiftedInput]
  by_cases hq : i.val < q
  · rw [dite_eq_left hq]
  · rw [dite_eq_right hq]
    have hi : ¬(1 ≤ i.val ∧ i.val < 1+n) := by omega
    rw [ite_eq_right hi]
    split_ifs <;> rfl

namespace PhysicalTree
lemma quarterZero_input (n N : ℕ) (j : Fin n) :
    quarterZero n N
      (Fin.natAdd 1 ((Fin.castAdd (n*n+Quarter.D n))
        ((Fin.castAdd (tensorWidth n (padding n)))
          (firstRegister n (width n) (launchWork n) j))))=N.testBit j.val := by
  simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,
    Fin.append_right,Fin.append_left,paddedZero,launchZero]
  change packed (launchWork n) (natBasis n N) (fun _ : Fin (width n) => false)
    ⟨j.val, by omega⟩ = _
  rw [packed_input]
  exact natBasis_apply n N j

lemma quarterWidth_input (n : ℕ) : 1+n≤quarterWidth n := by
  change 1+n≤1+(n+width n+launchWork n+tensorWidth n (padding n)+(n*n+Quarter.D n))
  omega

lemma quarterZero_shifted (n N : ℕ) : quarterZero n N=shiftedInput (quarterWidth n) n N := by
  funext i
  by_cases hi : 1 ≤ i.val ∧ i.val < 1+n
  · let j : Fin n:=⟨i.val-1,by omega⟩
    have he : i=Fin.natAdd 1 ((Fin.castAdd (n*n+Quarter.D n))
        ((Fin.castAdd (tensorWidth n (padding n)))
          (firstRegister n (width n) (launchWork n) j))) := by
      apply Fin.ext
      change i.val=1+(i.val-1)
      omega
    rw [he,quarterZero_input]
    change N.testBit (i.val-1)=_
    rw [←he]
    simp only [shiftedInput,ite_eq_left hi]
  · rw [quarterZero_clean n N i,shiftedInput,ite_eq_right hi]
    simpa only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and] using hi

lemma amplifiedZero_shifted (n N : ℕ) (hn : 0<n) :
    amplifiedZero n N hn=shiftedInput (amplifiedWidth n hn) n N := by
  rw [amplifiedZero,quarterZero_shifted,packed_shifted (quarterWidth_input n)]

lemma factoringZero_shifted (n N : ℕ) (hn : 0<n) :
    factoringZero n N hn=shiftedInput (readoutWidth n hn) n N := by
  rw [factoringZero,amplifiedZero_shifted]
  apply packed_shifted
  have hh:=quarterWidth_input n
  change 1+n≤quarterWidth n+1+reflectWork n hn
  omega
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
