import OAI.Combinatorics.ContingencyTables.Sampling.PaddedEnumerationBounds
import OAI.Combinatorics.ContingencyTables.Sampling.ExactBoxBounds
import OAI.Combinatorics.ContingencyTables.Transport.CanonicalDrawTabulation

namespace OAI

/-! # The completion boxes used at arbitrary enumerated profiles -/

namespace ContingencyTables.ProfilePrograms
open DensePrograms

lemma completionEnumeration_count (z : CompletionMargins) :
    gridStateCount (completionEnumerationData z)=
      (z.1.sum+1)^(z.1.tail.length*z.2.tail.length) := by
  rw [gridStateCount_eq]
  simp only [completionEnumerationData,List.length_map,zeroGrid,cellPairs,List.length_range]

lemma completionEnumeration_count_le (z : CompletionMargins) (m n N : ℕ)
    (hr : z.1.length ≤ m) (hc : z.2.length ≤ n) (hN : z.1.sum ≤ N) :
    gridStateCount (completionEnumerationData z) ≤ (N+1)^(m*n) := by
  rw [completionEnumeration_count]
  have hr' : z.1.tail.length ≤ m := by simp only [List.length_tail]; omega
  have hc' : z.2.tail.length ≤ n := by simp only [List.length_tail]; omega
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul hr' hc'))

lemma swapZeroList_length {A : Type} [MatchingFPRAS.TreeTyped.Codec A] [Inhabited A]
    (i : ℕ) (as : List A) : (DensePrograms.swapZeroList (i,as)).length=as.length := by
  simp only [swapZeroList,swapZeroIndices,List.length_map,List.length_range]

lemma swapZeroList_sum_le (i : ℕ) (as : List ℕ) :
    (DensePrograms.swapZeroList (i,as)).sum ≤ as.length*as.sum := by
  have h := list_sum_le_length_mul (DensePrograms.swapZeroList (i,as)) as.sum (by
    intro a ha
    rw [swapZeroList] at ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact list_getD_le_sum as (swapZeroIndex (i,j)))
  simpa only [swapZeroList_length] using h

lemma normalizedCompletion_count_le (z : CompletionMargins) (ij : ℕ×ℕ) :
    gridStateCount (completionEnumerationData (swapMargins (ij,z))) ≤
      (z.1.length*z.1.sum+1)^(z.1.length*z.2.length) := by
  apply completionEnumeration_count_le
  · simp only [swapMargins,swapZeroList_length,le_refl]
  · simp only [swapMargins,swapZeroList_length,le_refl]
  · exact swapZeroList_sum_le ij.1 z.1

lemma canonicalCompletion_count_le (z : CanonicalParameters) :
    gridStateCount (completionEnumerationData (canonicalCountInput z).1.1) ≤
      (z.1.1.length*z.1.1.sum+1)^(z.1.1.length*z.1.2.length) := by
  exact normalizedCompletion_count_le z.1 (DensePrograms.marginIndices z.1)

private def profilePaddingData (row : Bool) (z : ProfileCheckData×ℕ) : PaddingData :=
  let view := if row then z.1.1.1.2.1 else complementValues (z.1.2,z.1.1.1.2.2)
  let line : MarginCheckData := (((z.1.1.1.1,view),z.1.1.2),z.1.2)
  (line,z.2)

lemma profilePaddedMargins_length (row : Bool) (z : ProfileCheckData×ℕ) :
    (profilePaddedMargins row z).length ≤
      (if row then z.1.1.2.1 else z.1.1.2.2).length := by
  exact largePaddedMargins_length row (profilePaddingData row z)

lemma profilePaddedMargins_sum (row : Bool) (z : ProfileCheckData×ℕ) :
    (profilePaddedMargins row z).sum ≤
      (if row then z.1.1.2.1 else z.1.1.2.2).length*
        ((if row then z.1.1.2.1 else z.1.1.2.2).sum+
          (if !row then z.1.1.2.1 else z.1.1.2.2).length*z.2) := by
  exact largePaddedMargins_sum row (profilePaddingData row z)

lemma profilePaddedMargins_sum_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (v : ProfileCheckData) (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) (pad : ℕ) :
    (profilePaddedMargins true (v,pad)).sum+1 ≤ m*((List.ofFn r).sum+n*pad)+1 := by
  have hsum := profilePaddedMargins_sum true (v,pad)
  simp only [hr,hc,List.length_ofFn,ite_true,Bool.not_true,Bool.false_eq_true,ite_false] at hsum
  exact Nat.add_le_add_right hsum 1

/-- This bound is independent of the values in the two proposed small
views. In particular it applies before the validity test accepts them. -/
lemma profileCompletion_count (z : ProfileCheckData×ℕ) :
    gridStateCount (completionEnumerationData
      (profilePaddedMargins true z,profilePaddedMargins false z)) ≤
      (z.1.1.2.1.length*(z.1.1.2.1.sum+z.1.1.2.2.length*z.2)+1)^
        (z.1.1.2.1.length*z.1.1.2.2.length) := by
  apply completionEnumeration_count_le
  · simpa using profilePaddedMargins_length true z
  · simpa using profilePaddedMargins_length false z
  · simpa using profilePaddedMargins_sum true z

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] profilePaddedMargins

private lemma padded_base_bound (d b N m n : ℕ) (hd : 1 ≤ d) (hb : 1 ≤ b)
    (hm : m ≤ d) (hn : n ≤ d) (hN : N+1 ≤ 2^b) (hD : d^20+1 ≤ 2^b) :
    m*(N+n*d^12)+1 ≤ 2^(4*b) := by
  have hd20 : d ≤ d^20 := Nat.le_self_pow (by decide) d
  have hmP : m ≤ 2^b := hm.trans (hd20.trans (by omega))
  have hd14 : d^14 ≤ d^20 := Nat.pow_le_pow_right hd (by decide)
  have hpad : m*n*d^12 ≤ 2^b := by
    calc
      _ ≤ d*d*d^12 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hm hn)
      _ = d^14 := by ring
      _ ≤ 2^b := hd14.trans (by omega)
  have hprod : m*N ≤ (2^b)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hmP (show N ≤ 2^b by omega)
  have hP : 1 ≤ 2^b := one_le_pow₀ (by decide)
  have hP2 : 2^b ≤ (2^b)^2 := Nat.le_self_pow (by decide) _
  calc
    _ ≤ 4*(2^b)^2 := by nlinarith
    _ = 2^(2*b+2) := by rw [show 2*b=b*2 by omega,pow_add,pow_mul]; norm_num; ring
    _ ≤ 2^(4*b) := Nat.pow_le_pow_right (by decide) (by omega)

/-- All profile proposals have a singly exponential completion box,
including proposals rejected by the chain's validity test. -/
lemma arbitrary_profile_margin_sum {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) :
    let dim := dimensionAllowance (I := Fin m) (J := Fin n)
    (profilePaddedMargins true (v,dim^12)).sum+1 ≤ 2^(4*smallBinaryLength r c) := by
  dsimp only
  let dim := dimensionAllowance (I := Fin m) (J := Fin n)
  let bits := smallBinaryLength r c
  have hd : 1 ≤ dim := by unfold dim dimensionAllowance; omega
  have hm : m ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hn : n ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hN : (∑ i,r i)+1 ≤ 2^bits :=
    (show (∑ i,r i)+1 ≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hD : dim^20+1 ≤ 2^bits :=
    (show dim^20+1 ≤ stateBound r c+1 by unfold dim stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hbase := padded_base_bound dim bits (∑ i,r i) m n hd hb hm hn hN hD
  have hsum := profilePaddedMargins_sum_ofFn r c v hr hc (dim^12)
  rw [List.sum_ofFn] at hsum
  exact hsum.trans hbase

lemma arbitrary_profile_completion_count {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) :
    let dim := dimensionAllowance (I := Fin m) (J := Fin n)
    gridStateCount (completionEnumerationData
      (profilePaddedMargins true (v,dim^12),profilePaddedMargins false (v,dim^12))) ≤
      2^(4*(dim^2*smallBinaryLength r c)) := by
  dsimp only
  let dim := dimensionAllowance (I := Fin m) (J := Fin n)
  let bits := smallBinaryLength r c
  have hd : 1 ≤ dim := by unfold dim dimensionAllowance; omega
  have hm : m ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hn : n ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hN : (∑ i,r i)+1 ≤ 2^bits :=
    (show (∑ i,r i)+1 ≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hD : dim^20+1 ≤ 2^bits :=
    (show dim^20+1 ≤ stateBound r c+1 by unfold dim stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hbase := padded_base_bound dim bits (∑ i,r i) m n hd hb hm hn hN hD
  have hcount := profileCompletion_count (v,dim^12)
  simp only [hr,hc,List.length_ofFn,List.sum_ofFn] at hcount
  calc
    _ ≤ (m*((∑ i,r i)+n*dim^12)+1)^(m*n) := hcount
    _ ≤ (2^(4*bits))^(m*n) := Nat.pow_le_pow_left hbase _
    _ = 2^((4*bits)*(m*n)) := (pow_mul _ _ _).symm
    _ ≤ 2^(4*(dim^2*bits)) := Nat.pow_le_pow_right (by decide) (by
      have hh : m*n ≤ dim^2 := by simpa only [pow_two] using Nat.mul_le_mul hm hn
      nlinarith)

end
end ContingencyTables.SmallGraphProfiles

end OAI
