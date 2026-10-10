import OAI.NumberTheory.TotientAsymptotic.PrefixRecovery
import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCount

namespace OAI

/-! Restoring the common prefix does not multiply suffixes by witness choices. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma firstCollision_common_parts {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hi : 1 ≤ i) (hiR : i ≤ R x H)
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hq : q ∈ firstCollisionPairs x H t i) :
    q.1.head=q.2.head ∧ tupleInnerPrefix q.1 (i-1)=tupleInnerPrefix q.2 (i-1) := by
  obtain ⟨hl,hr,_,_,hcommon⟩ := firstCollisionPairs_data hPH hq
  refine ⟨?_,?_⟩
  · simpa only [wholeWitnessPrime,ite_true] using hcommon 0 hi
  · funext j
    have hj : j.val < R x H := by have := j.isLt; omega
    have he := hcommon (j.val+1) (by have := j.isLt; omega)
    rw [chosen_whole_prime hl.1 (by omega),chosen_whole_prime hr.1 (by omega)] at he
    change tuplePrimes q.1 (Fin.succ ⟨j.val,hj⟩)=tuplePrimes q.2 (Fin.succ ⟨j.val,hj⟩) at he
    simpa only [tupleInnerPrefix,dite_eq_left hj,tuplePrimes,Fin.cons_succ] using he

lemma collision_prefix_head_injective {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hi : 1 ≤ i) (hiR : i ≤ R x H)
    (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (p : Fin (i-1) → ℕ) :
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => q.1.head)
      (↑((firstCollisionPairs x H t i).filter
        (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p)) : Set _) := by
  intro q hq q' hq' he
  obtain ⟨hq,hs,hp⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq',hs',hp'⟩ := Finset.mem_filter.mp hq'
  have hc := firstCollision_common_parts hPH hi hiR hq
  have hc' := firstCollision_common_parts hPH hi hiR hq'
  have hl : q.1=q'.1 := tuple_recovered_from_parts hi (by omega) he (hp.trans hp'.symm)
    (congrArg Prod.fst (hs.trans hs'.symm))
  have hr : q.2=q'.2 := tuple_recovered_from_parts hi (by omega)
    (hc.1.symm.trans (he.trans hc'.1))
    (hc.2.symm.trans ((hp.trans hp'.symm).trans hc'.2))
    (congrArg Prod.snd (hs.trans hs'.symm))
  exact Prod.ext hl hr

/-- For each fixed suffix and common inner prefix, Chebyshev bounds the
number of admissible heads by the reciprocal of their exact denominator. -/
theorem collision_prefix_fiber_bound : ∀ᶠ x : ℝ in atTop,
    ∀ H i : ℕ, P H ≤ H → 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
    ∀ (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (p : Fin (i-1) → ℕ),
    (((firstCollisionPairs x H t i).filter
        (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p)).card : ℝ) ≤
      (10*x/Real.log x)*(prefixDenominator s.1 : ℝ)⁻¹*reciprocalShiftWeight p := by
  filter_upwards [largest_prime_count_upper,eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro H i hPH hi hiR t ht s p
  let Q := (firstCollisionPairs x H t i).filter
    (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p)
  by_cases hne : Q.Nonempty
  · obtain ⟨q,hq⟩ := hne
    obtain ⟨hq,hs,hp⟩ := Finset.mem_filter.mp hq
    have hl := (firstCollisionPairs_data hPH hq).1
    let D := (∏ j, (p j-1))*prefixDenominator s.1
    have hD : 0 < D := by
      have he := tupleValue_split_inner_suffix q.1 hi hiR
      rw [show tupleSuffix q.1 i=s.1 from congrArg Prod.fst hs,hp] at he
      have hv := basic_tuple_value_pos hPH hl.1
      change 0 < (∏ j, (p j-1))*prefixDenominator s.1
      rw [he,mul_assoc] at hv
      by_contra hnot
      have hz : (∏ j, (p j-1))*prefixDenominator s.1=0 := by omega
      rw [hz,mul_zero] at hv
      omega
    have hQ : ∀ a : ℕ, a ∈ Q.image (fun q => q.1.head) →
        a.Prime ∧ x^(9/10 : ℝ) ≤ a ∧ ((a-1)*D : ℕ) ≤ x := by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hq,hs,hp⟩ := Finset.mem_filter.mp hq
      have hl := (firstCollisionPairs_data hPH hq).1
      refine ⟨hl.1.1,hl.1.2.1,?_⟩
      have he := tupleValue_split_inner_suffix q.1 hi hiR
      rw [show tupleSuffix q.1 i=s.1 from congrArg Prod.fst hs,hp] at he
      have hv := hl.1.2.2.2.trans ht
      rw [he] at hv
      simpa only [D,mul_assoc] using hv
    have hb := hx D hD _ hQ
    rw [Finset.card_image_of_injOn (collision_prefix_head_injective hPH hi hiR s p)] at hb
    apply hb.trans_eq
    dsimp [D,reciprocalShiftWeight]
    simp only [Nat.cast_mul,Nat.cast_prod]
    ring
  · have hQ : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (Q.card : ℝ) ≤ _
    rw [hQ,Finset.card_empty,Nat.cast_zero]
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hl : 0 < Real.log x := Real.log_pos hx1
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (reciprocalShiftWeight_nonneg p)

end TotientAsymptotic

end

end OAI
