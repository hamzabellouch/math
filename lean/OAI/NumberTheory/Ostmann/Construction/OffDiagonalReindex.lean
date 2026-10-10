import OAI.NumberTheory.Ostmann.Construction.PivotFrequencyReindex
import OAI.NumberTheory.Ostmann.Construction.RemainingOffDiagonal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

def pivotPairWeight (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l) (p : ℕ) : ℂ :=
  (((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod:ℂ)*
    (Ostmann.smoothPartition (Real.log p-G):ℂ)*
    remainingIntegrand d P sources seed V giant X G bins outside l p u x v*
      conj (remainingIntegrand d P sources seed V giant X G bins outside l p u y w)

theorem pivotPairWeight_nonzero (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l) (p : ℕ)
    (hF : pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p≠0) :
    Ostmann.smoothPartition (Real.log p-G)≠0 ∧
      remainingIntegrand d P sources seed V giant X G bins outside l p u x v≠0 ∧
      remainingIntegrand d P sources seed V giant X G bins outside l p u y w≠0 := by
  have h1 := mul_ne_zero_iff.mp hF
  have h2 := mul_ne_zero_iff.mp h1.1
  have h3 := mul_ne_zero_iff.mp h2.1
  exact ⟨by exact_mod_cast h3.2,h2.2,by simpa only [map_ne_zero] using h1.2⟩

theorem mem_frequency_range_of_natAbs_le (V : ℕ→ℕ) (l : ℕ) (s : ℤ)
    (hs : s.natAbs≤V l) : s∈Finset.Icc (-(V l:ℤ)) (V l:ℤ) := by
  have h : |s|≤(V l:ℤ) := by
    simpa only [Int.natCast_natAbs] using (show (s.natAbs:ℤ)≤(V l:ℤ) by exact_mod_cast hs)
  exact Finset.mem_Icc.mpr (abs_le.mp h)

theorem pivotPair_frequency_reindex (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l)
    (hcut : ∀p∈integerPivotCell G,∀s,
      joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val=
        s*((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod*p →
      pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p≠0 → s.natAbs≤V (l+1)) :
    let N := joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val
    let U := ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod
    let F := pivotPairWeight d P sources seed V giant X G bins outside l u x y v w
    (∑p∈integerPivotCell G,if (U:ℤ)*(p:ℤ)∣N ∧ N≠0 then F p else 0)=
      ∑s:AllowedFrequency V (l+1),
        if N≠0 ∧ reversalPivot N U s.val∈integerPivotCell G ∧
          N=s.val*(U:ℤ)*(reversalPivot N U s.val:ℤ)
        then F (reversalPivot N U s.val) else 0 := by
  dsimp only
  let N := joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val
  let U := ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod
  let F := pivotPairWeight d P sources seed V giant X G bins outside l u x y v w
  change (∑p∈integerPivotCell G,if (U:ℤ)*(p:ℤ)∣N ∧ N≠0 then F p else 0)=
    ∑s:AllowedFrequency V (l+1),
      if N≠0 ∧ reversalPivot N U s.val∈integerPivotCell G ∧
        N=s.val*(U:ℤ)*(reversalPivot N U s.val:ℤ)
      then F (reversalPivot N U s.val) else 0
  by_cases hN : N=0
  · simp only [hN,ne_eq,not_true_eq_false,and_false,false_and,ite_false,Finset.sum_const_zero]
  · have he := pivot_frequency_reindex N hN U (assignedSlots_product_pos sources _ u)
      (integerPivotCell G) (fun p hp => (Finset.mem_Ioc.mp hp).1)
      (Finset.Icc (-(V (l+1):ℤ)) (V (l+1):ℤ)) F
      (fun p hp s hs hf => mem_frequency_range_of_natAbs_le V (l+1) s (hcut p hp s hs hf))
    simp only [hN,ne_eq,not_false_eq_true,and_true,true_and]
    rw [he]
    exact (Finset.sum_coe_sort _ _).symm

end Ostmann.Construction

end

end OAI
