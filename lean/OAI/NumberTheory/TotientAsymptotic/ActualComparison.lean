import OAI.NumberTheory.TotientAsymptotic.ChosenCollision
import OAI.NumberTheory.TotientAsymptotic.ResidualTupleRecovery
import OAI.NumberTheory.TotientAsymptotic.CollisionCount

namespace OAI

/-! Ford's comparison bound applied to finite families of actual tuple pairs. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def comparisonPairAt (x : ℝ) (H k : ℕ) (I : Finset ℕ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : ShiftedPair I.card where
  left := fun j => wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail)
    (I.orderEmbOfFin rfl j)
  right := fun j => wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail)
    (I.orderEmbOfFin rfl j)
  remainder := (suffixPreimage (chosenRemainder x H q.2.tail) k).totient

def comparisonEncoding (x : ℝ) (H k : ℕ) (I : Finset ℕ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : RecoveredPair I.card (R x H-k) :=
  (comparisonPairAt x H k I q,
    residualTupleData (chosenRemainder x H q.1.tail) k,
    residualTupleData (chosenRemainder x H q.2.tail) k)

lemma tuple_eq_of_head_tail {n : ℕ} {τ σ : TotientTuple n}
    (hh : τ.head=σ.head) (ht : τ.tail=σ.tail) : τ=σ := by
  cases τ
  cases σ
  simp_all

/-- Once the canceled primes and the common prefix are fixed, the comparison
data and the two residual tuples determine the ordered pair being counted. -/
theorem comparisonEncoding_injOn {x t : ℝ} {H k : ℕ} (I : Finset ℕ)
    (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)))
    (hL : L x H < m x) (hkL : k < L x H)
    (hQ : ∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2)
    (fixed : ℕ → ℕ × ℕ)
    (hfixed : ∀ q ∈ Q, ∀ r ≤ k, r ∉ I →
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) r=(fixed r).1 ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) r=(fixed r).2) :
    Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) := by
  intro q hq q' hq' he
  have hb := hQ q hq
  have hb' := hQ q' hq'
  have hd1 := congrArg (fun z : RecoveredPair I.card (R x H-k) => z.2.1) he
  have hd2 := congrArg (fun z : RecoveredPair I.card (R x H-k) => z.2.2) he
  have hwhole (r : ℕ) (hr : r ≤ k) :
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) r =
        wholeWitnessPrime q'.1.head (chosenRemainder x H q'.1.tail) r ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) r =
        wholeWitnessPrime q'.2.head (chosenRemainder x H q'.2.tail) r := by
    by_cases hrI : r ∈ I
    · have him : r ∈ Finset.univ.image (I.orderEmbOfFin rfl) := by
        rw [I.image_orderEmbOfFin_univ rfl]
        exact hrI
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp him
      exact ⟨congrArg (fun z : RecoveredPair I.card (R x H-k) => z.1.left j) he,
        congrArg (fun z : RecoveredPair I.card (R x H-k) => z.1.right j) he⟩
    · exact ⟨(hfixed q hq r hr hrI).1.trans (hfixed q' hq' r hr hrI).1.symm,
        (hfixed q hq r hr hrI).2.trans (hfixed q' hq' r hr hrI).2.symm⟩
  have hhead1 : q.1.head=q'.1.head := by
    simpa only [wholeWitnessPrime,ite_true] using (hwhole 0 (Nat.zero_le _)).1
  have hhead2 : q.2.head=q'.2.head := by
    simpa only [wholeWitnessPrime,ite_true] using (hwhole 0 (Nat.zero_le _)).2
  have hpref1 := prefix_recovered_from_residual (chosenRemainder_spec hb.1.2.2.1).1
    (chosenRemainder_spec hb'.1.2.2.1).1 hL hkL (by
      intro r hr
      have hh := (hwhole r (Finset.mem_Icc.mp hr).2).1
      simpa only [wholeWitnessPrime,ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega : r ≠ 0)] using hh) hd1
  have hpref2 := prefix_recovered_from_residual (chosenRemainder_spec hb.2.2.2.1).1
    (chosenRemainder_spec hb'.2.2.2.1).1 hL hkL (by
      intro r hr
      have hh := (hwhole r (Finset.mem_Icc.mp hr).2).2
      simpa only [wholeWitnessPrime,ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega : r ≠ 0)] using hh) hd2
  rw [(chosenRemainder_spec hb.1.2.2.1).2,(chosenRemainder_spec hb'.1.2.2.1).2] at hpref1
  rw [(chosenRemainder_spec hb.2.2.2.1).2,(chosenRemainder_spec hb'.2.2.2.1).2] at hpref2
  exact Prod.ext (tuple_eq_of_head_tail hhead1 hpref1) (tuple_eq_of_head_tail hhead2 hpref2)

/-- This is the quantitative comparison for a single fixed canceled-index,
grid, and residual-integer class. All counted objects are actual tuple pairs;
the missing coordinates are restored by prime-occurrence allocation. -/
theorem actual_comparison_with_recovery (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ {x t : ℝ} {H k K D r : ℕ} (I : Finset ℕ) (y S : ℝ) (Y U : ℕ → ℝ),
      y₀ ≤ y → FordComparisonParameters I.card y S D r Y U →
      L x H < m x → R x H < L x H → k < L x H →
      ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
      (∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2) →
      ∀ fixed : ℕ → ℕ × ℕ,
      (∀ q ∈ Q, ∀ j ≤ k, j ∉ I →
        wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j=(fixed j).1 ∧
        wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j=(fixed j).2) →
      (∀ q ∈ Q, (suffixPreimage (chosenRemainder x H q.1.tail) k).totient=D) →
      (∀ q ∈ Q, (comparisonPairAt x H k I q).remainder.primeFactorsList.length ≤ K) →
      (∀ q ∈ Q, FordComparisonConditions I.card y S D r Y U (comparisonPairAt x H k I q)) →
      (Q.card : ℝ) ≤ (((R x H-k : ℕ) : ℝ)+1)^(D.primeFactorsList.length+K)*
        fordComparisonBound C I.card y S D r Y U := by
  obtain ⟨C,y₀,hC,hy₀,hbound⟩ := ford_comparison_with_recovery hford
  refine ⟨C,y₀,hC,hy₀,?_⟩
  intro x t H k K D r I y S Y U hy hparam hL hR hk Q hQ fixed hfixed hD hK hcond
  let T := Q.image (comparisonEncoding x H k I)
  have hinj := comparisonEncoding_injOn I Q hL hk hQ fixed hfixed
  have hcard : T.card=Q.card := Finset.card_image_of_injOn hinj
  have hb := hbound I.card (R x H-k) K y S D r Y U hy hparam T
    (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact hcond q hq)
    (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact hK q hq)
    (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨residualTupleData_primes (chosenRemainder_spec (hQ q hq).1.2.2.1).1 hR.le,
        residualTupleData_primes (chosenRemainder_spec (hQ q hq).2.2.2.1).1 hR.le⟩)
    (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨(residualTupleData_denominator (chosenRemainder_spec (hQ q hq).1.2.2.1).1 hL hR).trans (hD q hq),
        residualTupleData_denominator (chosenRemainder_spec (hQ q hq).2.2.2.1).1 hL hR⟩)
  simpa only [hcard] using hb

end TotientAsymptotic

end

end OAI
