import OAI.NumberTheory.TotientAsymptotic.CollisionClassData

namespace OAI

/-! Actual tuple suffixes, with the common prefix removed exactly once. -/

noncomputable section

namespace TotientAsymptotic

def tupleSuffix {R : ℕ} (τ : TotientTuple R) (i : ℕ) : PrefixDatum (R+1-i) where
  primes := fun j => tuplePrimes τ ⟨i+j.val,by have := j.isLt; omega⟩
  d := τ.tail.d

def pairSuffix {R : ℕ} (q : TotientTuple R × TotientTuple R) (i : ℕ) :
    PrefixDatum (R+1-i) × PrefixDatum (R+1-i) := (tupleSuffix q.1 i,tupleSuffix q.2 i)

lemma chosen_whole_prime {x t : ℝ} {H j : ℕ} {τ : TotientTuple (R x H)}
    (hτ : IsBasicTuple x H t τ) (hj : j ≤ R x H) :
    wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j =
      tuplePrimes τ ⟨j,by omega⟩ := by
  have he := wholeWitnessPrime_tuple (p := τ.head)
    (η := chosenRemainder x H τ.tail) ⟨j,by omega⟩
  rw [chosenRemainder_tuple hτ] at he
  exact he

/-- Comparison primes and residual tuples recover only the suffix being
counted; the earlier common prefix is irrelevant to this reconstruction. -/
theorem tupleSuffix_recovered {x t : ℝ} {H i k : ℕ}
    {τ σ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) (hσ : IsBasicTuple x H t σ)
    (hL : L x H < m x) (hkL : k < L x H) (hiR : i ≤ R x H)
    (hknown : ∀ r ∈ Finset.Icc i k,
      wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) r =
        wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) r)
    (hdata : residualTupleData (chosenRemainder x H τ.tail) k =
      residualTupleData (chosenRemainder x H σ.tail) k) :
    tupleSuffix τ i=tupleSuffix σ i := by
  let η := chosenRemainder x H τ.tail
  let ξ := chosenRemainder x H σ.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hτ.2.2.1).1
  have hξ : IsBasicRemainder x H ξ := (chosenRemainder_spec hσ.2.2.1).1
  have hps := congrArg PrefixDatum.primes hdata
  have hds := congrArg PrefixDatum.d hdata
  have hp : (tupleSuffix τ i).primes=(tupleSuffix σ i).primes := by
    funext j
    have hj : i+j.val ≤ R x H := by have := j.isLt; omega
    change tuplePrimes τ ⟨i+j.val,by omega⟩=tuplePrimes σ ⟨i+j.val,by omega⟩
    rw [← chosen_whole_prime hτ hj,← chosen_whole_prime hσ hj]
    by_cases hr : i+j.val ≤ k
    · exact hknown _ (Finset.mem_Icc.mpr ⟨by omega,hr⟩)
    · let l : Fin (R x H-k) := ⟨i+j.val-k-1,by omega⟩
      have he := congrFun hps l
      change remainderPrime η (k+l.val+1)=remainderPrime ξ (k+l.val+1) at he
      have hidx : k+l.val+1=i+j.val := by dsimp [l]; omega
      rw [hidx] at he
      simpa only [wholeWitnessPrime,ite_eq_right (by omega : i+j.val ≠ 0)] using he
  have ht : (tupleSuffix τ i).d=(tupleSuffix σ i).d := by
    have htailτ : (remainderTail x H η).totient=τ.tail.d :=
      congrArg PrefixDatum.d (chosenRemainder_spec hτ.2.2.1).2
    have htailσ : (remainderTail x H ξ).totient=σ.tail.d :=
      congrArg PrefixDatum.d (chosenRemainder_spec hσ.2.2.1).2
    change τ.tail.d=σ.tail.d
    rw [← htailτ,← htailσ]
    by_cases hk : k ≤ R x H
    · simpa only [residualTupleData,ite_eq_left hk] using hds
    · have hd : (suffixPreimage η k).totient=(suffixPreimage ξ k).totient := by
        simpa only [residualTupleData,ite_eq_right hk] using hds
      rw [← suffixPreimage_at_R η,← suffixPreimage_at_R ξ,
        basic_suffix_totient_split hη hL (by omega : R x H ≤ k) hkL,
        basic_suffix_totient_split hξ hL (by omega : R x H ≤ k) hkL,hd]
      congr 1
      apply Finset.prod_congr rfl
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have he := hknown r (Finset.mem_Icc.mpr ⟨by omega,hr'.2⟩)
      have hprime : remainderPrime η r=remainderPrime ξ r := by
        simpa only [wholeWitnessPrime,ite_eq_right (by omega : r ≠ 0)] using he
      exact congrArg (fun n : ℕ => n-1) hprime
  exact congrArg₂ PrefixDatum.mk hp ht

end TotientAsymptotic

end

end OAI
