import OAI.NumberTheory.TotientAsymptotic.CollisionTuples

namespace OAI

/-! Exact comparison data extracted from two basic witnesses for colliding tuples. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def wholeWitnessPrime {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H))
    (i : ℕ) : ℕ := if i=0 then p else remainderPrime η i

def witnessTuple {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) :
    TotientTuple (R x H) := ⟨p, prefixOfRemainder x H η⟩

lemma wholeWitness_shift_product {x : ℝ} {H k : ℕ} (p : ℕ)
    (η : RemainderDatum (L x H)) :
    (∏ r ∈ Finset.Icc 0 k, (wholeWitnessPrime p η r-1)) =
      (p-1)*∏ r ∈ Finset.Icc 1 k, (remainderPrime η r-1) := by
  have hsplit : Finset.Icc 0 k = insert 0 (Finset.Icc 1 k) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.prod_insert (by simp)]
  simp only [wholeWitnessPrime, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  rw [ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega)]

/-- Every valid cutoff gives the same integer value. No witness representative
is discarded from the tail totient. -/
lemma witness_tuple_value_at_cut {x : ℝ} {H k : ℕ} {p : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hR : R x H < L x H) (hk : k < L x H) :
    tupleValue (witnessTuple p η) = (suffixPreimage η k).totient *
      ∏ r ∈ Finset.Icc 0 k, (wholeWitnessPrime p η r-1) := by
  have hRsplit := basic_suffix_totient_split hη hL (Nat.zero_le (R x H)) hR
  have hksplit := basic_suffix_totient_split hη hL (Nat.zero_le k) hk
  simp only [Nat.zero_add] at hRsplit hksplit
  have hprod : (∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1)) =
      ∏ r ∈ Finset.Icc 1 (R x H), (remainderPrime η r-1) :=
    prod_fin_shifted (R x H) (fun r => (remainderPrime η r-1))
  unfold tupleValue witnessTuple tuplePrimes prefixOfRemainder
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hprod]
  rw [← suffixPreimage_at_R η, wholeWitness_shift_product]
  calc
    _ = (p-1)*((suffixPreimage η (R x H)).totient*
        ∏ r ∈ Finset.Icc 1 (R x H), (remainderPrime η r-1)) := by ring
    _ = (p-1)*(suffixPreimage η 0).totient := by rw [hRsplit]
    _ = _ := by rw [hksplit]; ring

/-- Cancel all matched primes up to the cutoff, including the common prefix.
The first differing prime survives, and at most `k-i+1` indices survive. -/
theorem witness_collision_cancel {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hξ : IsBasicRemainder x H ξ)
    (hp : p.Prime) (hL : L x H < m x) (hR : R x H < L x H)
    (hk : k < L x H) (hik : i ≤ k)
    (hv : tupleValue (witnessTuple p η) = tupleValue (witnessTuple q ξ))
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hcommon : ∀ j < i, wholeWitnessPrime p η j = wholeWitnessPrime q ξ j) :
    let I := (Finset.Icc 0 k).filter (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j)
    (suffixPreimage η k).totient*(∏ j ∈ I, (wholeWitnessPrime p η j-1)) =
      (suffixPreimage ξ k).totient*(∏ j ∈ I, (wholeWitnessPrime q ξ j-1)) ∧
    i ∈ I ∧ I.card ≤ k-i+1 := by
  classical
  dsimp only
  have hval : (suffixPreimage η k).totient*
      (∏ j ∈ Finset.Icc 0 k, (wholeWitnessPrime p η j-1)) =
      (suffixPreimage ξ k).totient*
      (∏ j ∈ Finset.Icc 0 k, (wholeWitnessPrime q ξ j-1)) := by
    simpa only [witness_tuple_value_at_cut hη hL hR hk,
      witness_tuple_value_at_cut hξ hL hR hk] using hv
  refine ⟨cancel_equal_shifts _ _ _ _ _ ?_ hval, ?_, ?_⟩
  · intro j hj
    by_cases hj0 : j=0
    · simp only [wholeWitnessPrime, hj0, ite_true]
      exact hp.two_le
    · simp only [wholeWitnessPrime, ite_eq_right hj0]
      exact (hη.2.1 j (Finset.mem_Icc.mpr
        ⟨by omega, (Finset.mem_Icc.mp hj).2.trans hk.le⟩)).1.two_le
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hik⟩, hfirst⟩
  · have hsub : (Finset.Icc 0 k).filter
        (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j) ⊆ Finset.Icc i k := by
      intro j hj
      obtain ⟨hj, hne⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hj).2⟩
      by_contra! hh
      exact hne (hcommon j hh)
    have hh := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hh
    omega

end TotientAsymptotic

end

end OAI
