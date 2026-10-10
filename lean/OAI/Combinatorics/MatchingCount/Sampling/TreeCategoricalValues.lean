import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeCategorical

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma cumulativeFraction_val_ofFn {r : ℕ} (q : Fin r → Fraction) (hq : ∀ i,0<(q i).2) (n : ℕ) :
    val (cumulativeFraction (List.ofFn q,n))=FiniteChoice.cumulative (fun i=>val (q i)) n := by
  rw [cumulativeFraction,sum_val]
  · simp only [List.map_take,List.map_ofFn,Function.comp_apply,List.sum_take_ofFn,
      FiniteChoice.cumulative,Finset.sum_filter]
  · intro b hb
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hb)
    subst b
    exact hq i
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction

lemma choose_values {r K : ℕ} (q : Fin r → Fraction) (hq : ∀ i,0<(q i).2)
    (hs : ∑ i,val (q i)=1) (hK : 0<K) (J : Fin K) :
    choose (List.ofFn q,(J.val,K))=(FiniteChoice.choose (fun i=>val (q i)) hs hK J).val := by
  let j := FiniteChoice.choose (fun i=>val (q i)) hs hK J
  have hpred (i : ℕ) : predicate ((List.ofFn q,(J.val,K)),i)=
      decide ((J.val:ℚ)/K<FiniteChoice.cumulative (fun i=>val (q i)) (i+1)) := by
    rw [predicate,less_val (J.val,K) (cumulativeFraction (List.ofFn q,i+1)) hK (sum_den _),cumulativeFraction_val_ofFn q hq]
    rfl
  unfold choose
  simp only [List.length_ofFn]
  apply le_antisymm
  · apply listMin_le
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq]
    exact ⟨j.isLt,FiniteChoice.choose_upper _ hs hK J⟩
  · apply le_listMin j.isLt.le
    intro i hi
    simp only [List.mem_filter,List.mem_range,hpred,decide_eq_true_eq] at hi
    exact FiniteChoice.choose_le _ hs hK J ⟨i,hi.1⟩ hi.2

lemma bitValue_ofFn (k : ℕ) (bits : Fin k → Bool) :
    StackAddition.value (List.ofFn bits)=(FiniteChoice.tapeIndex k bits).val := by
  have hv' (k : ℕ) (bits : Fin k → Bool) :
      StackAddition.value (List.ofFn bits)=∑ i, (if bits i then 1 else 0)*2^i.val := by
    induction k with
    | zero => simp [StackAddition.value]
    | succ k ih =>
      rw [List.ofFn_succ,StackAddition.value,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
      rw [Finset.mul_sum]
      rw [Bool.toNat,Bool.cond_eq_ite]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [FiniteChoice.tapeIndex_value,hv']

lemma chooseBits_values {r k : ℕ} (q : Fin r → Fraction) (hq : ∀ i,0<(q i).2)
    (hs : ∑ i,val (q i)=1) (bits : Fin k → Bool) :
    chooseBits (List.ofFn q,List.ofFn bits)=
      (FiniteChoice.chooseBits (fun i=>val (q i)) hs k bits).val := by
  rw [chooseBits,bitDenominator_eq,List.length_ofFn,bitValue_ofFn]
  exact choose_values q hq hs (by positivity) (FiniteChoice.tapeIndex k bits)
end MatchingFPRAS.ExecutableChoice

end OAI
