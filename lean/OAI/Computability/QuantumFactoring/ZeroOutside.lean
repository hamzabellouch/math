import Mathlib
import OAI.Computability.QuantumFactoring.TreeReadOnly

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork Exactness

/-- A linear-size clean-work flag, leaving every protected input bit alone. -/
def zeroOutside {q : ℕ} (I : Finset (Fin q)) : BooleanNetwork q 1 :=
  all (List.ofFn (fun i : Fin q => if i∈I then constant true else (bit i).bnot))

lemma zeroOutside_value {q : ℕ} (I : Finset (Fin q)) (x : Basis q) :
    (zeroOutside I).eval x 0=true ↔ ∀ i, i∉I → x i=false := by
  simp only [zeroOutside,all_eval,List.mem_ofFn]
  constructor
  · intro h i hi
    have hh:=h _ ⟨i,rfl⟩
    simpa only [ite_eq_right hi,eval_bnot,eval_bit,Bool.not_eq_true'] using hh
  · intro h c hc
    obtain ⟨i,rfl⟩:=hc
    by_cases hi : i∈I
    · simp only [ite_eq_left hi,eval_constant]
    · simp only [ite_eq_right hi,eval_bnot,eval_bit,h i hi,Bool.not_false]

lemma zeroOutside_count {q : ℕ} (I : Finset (Fin q)) : (zeroOutside I).net.count≤2*q+1 := by
  have h : ∀ c∈List.ofFn (fun i : Fin q => if i∈I then constant true else (bit i).bnot),
      c.net.count≤1 := by
    intro c hc
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
    by_cases hi : i∈I
    · rw [ite_eq_left hi]
      exact le_rfl
    · rw [ite_eq_right hi]
      exact le_rfl
  simpa only [zeroOutside,List.length_ofFn,Nat.reduceAdd,Nat.mul_comm] using all_count _ h

lemma zeroOutside_sector {q : ℕ} (I : Finset (Fin q)) (z : Basis q)
    (hz : ∀ i, i∉I → z i=false) (x : Basis q) (hx : inputSector I z x) :
    (zeroOutside I).eval x 0=true ↔ x=z := by
  rw [zeroOutside_value]
  constructor
  · intro h
    funext i
    by_cases hi : i∈I
    · exact hx i hi
    · rw [h i hi,hz i hi]
  · rintro rfl
    exact hz

lemma tensorLayout_zero (q k : ℕ) :
    tensorLayout q k (fun _ _=>false)=(fun _=>false) := by
  induction k with
  | zero=>funext i;exact Fin.elim0 i
  | succ k ih=>
    rw [tensorLayout_succ]
    change Fin.append (fun _=>false) (tensorLayout q k (fun _ _=>false))=_
    rw [ih]
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.append_left,Fin.append_right]

namespace PhysicalTree
lemma launchZero_suffix (n N : ℕ) (i : Fin (launchWidth n)) (hi : n ≤ i.val) :
    launchZero n N i=false := by
  simp only [launchZero,packed,dite_eq_right (Nat.not_lt.mpr hi)]
  split_ifs <;> rfl

lemma paddedZero_suffix (n N : ℕ) (i : Fin (paddedWidth n)) (hi : n ≤ i.val) :
    paddedZero n N i=false := by
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro j hj
    simpa only [paddedZero,Fin.append_left] using launchZero_suffix n N j hj
  · intro j _hj
    simp only [paddedZero,Fin.append_right]
    change tensorLayout n (padding n) (fun _ _=>false) j=false
    rw [tensorLayout_zero]

lemma quarterZero_clean (n N : ℕ) (i : Fin (quarterWidth n)) (hi : i∉inputWires n) :
    quarterZero n N i=false := by
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro j _hj
    simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,Fin.append_left]
  · intro j hj
    simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,Fin.append_right]
    change Fin.append (paddedZero n N) (Fin.append (fun _ : Fin (n*n)=>false)
      (fun _ : Fin (Quarter.D n)=>false)) j=false
    have hn : n ≤ j.val := by
      have hh : ¬(1 ≤ 1+j.val ∧ 1+j.val < 1+n) := by
        simpa only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and,
          Fin.val_natAdd] using hj
      omega
    clear hj
    revert hn
    refine Fin.addCases ?_ ?_ j
    · intro a ha
      simpa only [Fin.append_left] using paddedZero_suffix n N a ha
    · intro a _ha
      simp only [Fin.append_right]
      refine Fin.addCases ?_ ?_ a <;> intro j <;> simp only [Fin.append_left,Fin.append_right]

/-- The zero reflection's flag depends only on the length and the actual clean
work coordinates, never on the unknown integer or its factorization. -/
def zeroNet (n : ℕ) : BooleanNetwork (quarterWidth n) 1 := zeroOutside (inputWires n)

lemma zeroNet_count (n : ℕ) : (zeroNet n).net.count≤2*quarterWidth n+1 :=
  zeroOutside_count _

lemma zeroNet_sector (n N : ℕ) (x : Basis (quarterWidth n))
    (hx : inputSector (inputWires n) (quarterZero n N) x) :
    (zeroNet n).eval x 0=true ↔ x=quarterZero n N :=
  zeroOutside_sector _ _ (quarterZero_clean n N) _ hx

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
