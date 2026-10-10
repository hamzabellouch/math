import OAI.NumberTheory.TotientAsymptotic.TupleSuffix
import OAI.NumberTheory.TotientAsymptotic.PrefixSize
import OAI.NumberTheory.TotientAsymptotic.SurvivingBlockSize

namespace OAI

/-! Exact values of the suffix data used in the collision quotient. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma tupleSuffix_denominator_product {n i : ℕ} (τ : TotientTuple n) (hi : i ≤ n) :
    prefixDenominator (tupleSuffix τ i) =
      τ.tail.d*∏ j ∈ Finset.Ici (⟨i,by omega⟩ : Fin (n+1)), (tuplePrimes τ j-1) := by
  unfold prefixDenominator tupleSuffix
  congr 1
  apply Finset.prod_bij (fun j _ => (⟨i+j.val,by have := j.isLt; omega⟩ : Fin (n+1)))
  · intro j _
    exact Finset.mem_Ici.mpr (by change i ≤ i+j.val; omega)
  · intro j _ k _ he
    apply Fin.ext
    have he' := congrArg Fin.val he
    dsimp only at he'
    omega
  · intro j hj
    have hj' : i ≤ j.val := by
      have hh := Finset.mem_Ici.mp hj
      exact hh
    refine ⟨⟨j.val-i,by have := j.isLt; omega⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    dsimp only
    omega
  · intro j _
    rfl

lemma tupleSuffix_denominator_eq_of_collision {n i : ℕ} {τ σ : TotientTuple n}
    (hi : i ≤ n) (hp : ∀ j, 2 ≤ tuplePrimes τ j)
    (hv : tupleValue τ=tupleValue σ)
    (hcommon : ∀ j : Fin (n+1), j.val < i → tuplePrimes τ j=tuplePrimes σ j) :
    prefixDenominator (tupleSuffix τ i)=prefixDenominator (tupleSuffix σ i) := by
  rw [tupleSuffix_denominator_product τ hi,tupleSuffix_denominator_product σ hi]
  exact tuple_collision_suffix_identity hp hv ⟨i,by omega⟩ hcommon

lemma tupleSuffix_denominator_whole {x t : ℝ} {H i : ℕ}
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) (hi : i ≤ R x H) :
    prefixDenominator (tupleSuffix τ i)=τ.tail.d*
      ∏ j ∈ Finset.Icc i (R x H),
        (wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j-1) := by
  unfold prefixDenominator tupleSuffix
  congr 1
  apply Finset.prod_bij (fun j _ => i+j.val)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩
  · intro j _ k _ he
    apply Fin.ext
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact ⟨⟨j-i,by omega⟩,Finset.mem_univ _,by dsimp; omega⟩
  · intro j _
    rw [chosen_whole_prime hτ (by have := j.isLt; omega)]

lemma tupleSuffix_denominator_positive {x t : ℝ} {H i : ℕ}
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ)
    (hL : L x H < m x) (hR : R x H < L x H) (hi : 1 ≤ i) (hiR : i ≤ R x H) :
    prefixDenominator (tupleSuffix τ i)=
      (remainderPrime (chosenRemainder x H τ.tail) i-1)*
        (suffixPreimage (chosenRemainder x H τ.tail) i).totient := by
  let η := chosenRemainder x H τ.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hτ.2.2.1).1
  have hd : τ.tail.d=(suffixPreimage η (R x H)).totient := by
    have hd' := congrArg PrefixDatum.d (chosenRemainder_spec hτ.2.2.1).2
    change (remainderTail x H (chosenRemainder x H τ.tail)).totient=τ.tail.d at hd'
    rw [← suffixPreimage_at_R] at hd'
    exact hd'.symm
  rw [tupleSuffix_denominator_whole hτ hiR,hd]
  have hp : (∏ j ∈ Finset.Icc i (R x H),
      (wholeWitnessPrime τ.head η j-1)) =
      ∏ j ∈ Finset.Icc i (R x H), (remainderPrime η j-1) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [wholeWitnessPrime,ite_eq_right (by have := (Finset.mem_Icc.mp hj).1; omega : j ≠ 0)]
  rw [hp]
  have hs : Finset.Icc i (R x H)=insert i (Finset.Icc (i+1) (R x H)) := by
    ext j
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  rw [hs,Finset.prod_insert (by simp),basic_suffix_totient_split hη hL hiR hR]
  ring

lemma tupleSuffix_denominator_block {x t : ℝ} {H i k : ℕ}
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ)
    (hL : L x H < m x) (hR : R x H < L x H)
    (hi : 1 ≤ i) (hiR : i ≤ R x H) (hik : i ≤ k) (hk : k < L x H) :
    prefixDenominator (tupleSuffix τ i)=
      witnessBlockValue τ.head (chosenRemainder x H τ.tail) i k := by
  rw [tupleSuffix_denominator_positive hτ hL hR hi hiR,
    witnessBlockValue_positive (chosenRemainder_spec hτ.2.2.1).1 hL hi hik hk]

end TotientAsymptotic

end

end OAI
