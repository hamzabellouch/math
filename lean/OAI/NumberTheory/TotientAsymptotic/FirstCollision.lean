import OAI.NumberTheory.TotientAsymptotic.SuffixRepresentatives
import OAI.NumberTheory.TotientAsymptotic.SuffixArithmetic
import OAI.NumberTheory.TotientAsymptotic.CollisionDyadicSize

namespace OAI

/-! The actual first-difference partition and its suffix quotient. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def FirstDifferenceAt {x : ℝ} {H : ℕ} (i : ℕ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : Prop :=
  wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) i ≠
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) i ∧
  ∀ j < i, wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j =
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j

def firstCollisionPairs (x : ℝ) (H : ℕ) (t : ℝ) (i : ℕ) :
    Finset (TotientTuple (R x H) × TotientTuple (R x H)) :=
  (goodCollisionPairs x H t).filter (FirstDifferenceAt i)

def firstCollisionSuffixes (x : ℝ) (H : ℕ) (t : ℝ) (i : ℕ) :
    Finset (PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) :=
  (firstCollisionPairs x H t i).image (fun q => pairSuffix q i)

lemma firstCollisionPairs_data {x t : ℝ} {H i : ℕ} (hPH : P H ≤ H)
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hq : q ∈ firstCollisionPairs x H t i) :
    IsGoodTuple x H t q.1 ∧ IsGoodTuple x H t q.2 ∧
    tupleValue q.1=tupleValue q.2 ∧ FirstDifferenceAt i q := by
  obtain ⟨hq,hfirst⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpair,_,hv⟩ := Finset.mem_filter.mp hq
  obtain ⟨hl,hr⟩ := Finset.mem_product.mp hpair
  exact ⟨(mem_goodTupleFinset hPH).mp hl,(mem_goodTupleFinset hPH).mp hr,hv,hfirst⟩

lemma firstCollisionSuffixes_equal_value {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hi : i ≤ R x H)
    {s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)}
    (hs : s ∈ firstCollisionSuffixes x H t i) :
    prefixDenominator s.1=prefixDenominator s.2 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hl,hr,hv,_,hcommon⟩ := firstCollisionPairs_data hPH hq
  apply tupleSuffix_denominator_eq_of_collision hi
    (fun j => (basic_tuple_primes hPH hl.1 j).two_le) hv
  intro j hj
  rw [← chosen_whole_prime hl.1 (by have := j.isLt; omega),
    ← chosen_whole_prime hr.1 (by have := j.isLt; omega)]
  exact hcommon j.val hj

/-- Every actual positive first-difference pair lies in Ford's counting
block at its suffix's dyadic endpoint. This holds for both chosen witnesses. -/
theorem first_collision_dyadic_blocks : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → L x H < m x → R x H < L x H →
    ∀ t y : ℝ, ∀ q ∈ firstCollisionPairs x H t i,
    y/2 < (prefixDenominator (tupleSuffix q.1 i) : ℝ) →
    (prefixDenominator (tupleSuffix q.1 i) : ℝ) ≤ y →
    GoodCollisionBlock x t H i y q ∧
    (87/100 : ℝ)*fordBandScale x i ≤ B y ∧ B y ≤ (113/100 : ℝ)*fordBandScale x i := by
  filter_upwards [collision_suffix_dyadic_size,eventually_collision_indices,
    eventually_tail_cut_separated] with H hsize hind hsep
  filter_upwards [hsize,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi hiR hL hR t y q hq hlo hhi
  obtain ⟨hl,hr,hv,hfirst,hcommon⟩ := firstCollisionPairs_data (by omega) hq
  have hiL : i+2 ≤ L x H := by unfold R L at *; omega
  have hk : collisionLastIndex x i < L x H := (hind x hm i hiR).2.2
  have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
  have hsame : prefixDenominator (tupleSuffix q.1 i)=prefixDenominator (tupleSuffix q.2 i) :=
    firstCollisionSuffixes_equal_value (by omega) hiR (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hdleft := tupleSuffix_denominator_positive hl.1 hL hR hi hiR
  have hdright := tupleSuffix_denominator_positive hr.1 hL hR hi hiR
  have hls := hx i hi hiR hiL hL _ (chosenRemainder_spec hl.1.2.2.1).1 y
    (by rwa [← hdleft]) (by rwa [← hdleft])
  have hrs := hx i hi hiR hiL hL _ (chosenRemainder_spec hr.1.2.2.1).1 y
    (by rwa [← hdright,← hsame]) (by rwa [← hdright,← hsame])
  refine ⟨⟨hl,hr,hv,hfirst,hcommon,?_,?_,?_,?_⟩,hls.2.1,hls.2.2⟩
  · simpa only [wholeWitnessPrime,ite_eq_right (by omega : i ≠ 0)] using hls.1
  · simpa only [wholeWitnessPrime,ite_eq_right (by omega : i ≠ 0)] using hrs.1
  · rwa [← tupleSuffix_denominator_block hl.1 hL hR hi hiR hik hk]
  · intro hzero
    omega

end TotientAsymptotic

end

end OAI
