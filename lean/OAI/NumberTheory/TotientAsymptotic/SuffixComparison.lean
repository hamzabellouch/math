import OAI.NumberTheory.TotientAsymptotic.TupleSuffix
import OAI.NumberTheory.TotientAsymptotic.FordKernel

namespace OAI

/-! The comparison count for distinct suffixes after removing a varying prefix. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma tupleSuffix_zero_injective (R : ℕ) : Function.Injective (fun τ : TotientTuple R => tupleSuffix τ 0) := by
  intro τ σ he
  have hp := congrArg PrefixDatum.primes he
  have hd := congrArg PrefixDatum.d he
  have hh : τ.head=σ.head := by
    have h := congrFun hp ⟨0,by omega⟩
    simpa [tupleSuffix,tuplePrimes] using h
  have htp : τ.tail.primes=σ.tail.primes := by
    funext j
    have h := congrFun hp j.succ
    simpa [tupleSuffix,tuplePrimes] using h
  exact tuple_eq_of_head_tail hh (congrArg₂ PrefixDatum.mk htp hd)

lemma pairSuffix_zero_injective (R : ℕ) : Function.Injective (fun q : TotientTuple R × TotientTuple R => pairSuffix q 0) := by
  intro q q' he
  exact Prod.ext (tupleSuffix_zero_injective R (congrArg Prod.fst he))
    (tupleSuffix_zero_injective R (congrArg Prod.snd he))

/-- Comparison data need determine only the suffix, because representatives
of distinct suffix pairs are selected before applying this estimate. -/
theorem comparisonEncoding_injOn_of_suffix {x t : ℝ} {H i k : ℕ}
    (I : Finset ℕ) (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)))
    (hL : L x H < m x) (hk : k < L x H) (hi : i ≤ R x H)
    (hQ : ∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2)
    (hdet : Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _))
    (fixed : ℕ → ℕ × ℕ)
    (hfixed : ∀ q ∈ Q, ∀ r ∈ Finset.Icc i k, r ∉ I →
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) r=(fixed r).1 ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) r=(fixed r).2) :
    Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) := by
  intro q hq q' hq' he
  have hwhole (r) (hr : r ∈ Finset.Icc i k) :
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) r=
        wholeWitnessPrime q'.1.head (chosenRemainder x H q'.1.tail) r ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) r=
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
  apply hdet hq hq'
  apply Prod.ext
  · exact tupleSuffix_recovered (hQ q hq).1 (hQ q' hq').1 hL hk hi
      (fun r hr => (hwhole r hr).1)
      (congrArg (fun z : RecoveredPair I.card (R x H-k) => z.2.1) he)
  · exact tupleSuffix_recovered (hQ q hq).2 (hQ q' hq').2 hL hk hi
      (fun r hr => (hwhole r hr).2)
      (congrArg (fun z : RecoveredPair I.card (R x H-k) => z.2.2) he)

lemma fixed_canceled_coordinates {x : ℝ} {H i k : ℕ}
    (I : Finset ℕ) (q : TotientTuple (R x H) × TotientTuple (R x H))
    (v : Fin (canceledIndices i k I).card → ℕ)
    (hI : collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i k=I)
    (hv : canceledPrimesAt x H i k I q.1=v) :
    ∀ j ∈ Finset.Icc i k, j ∉ I →
      let a := if h : j ∈ canceledIndices i k I then
        v (((canceledIndices i k I).orderIsoOfFin rfl).symm ⟨j,h⟩) else 1
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j=a ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j=a := by
  intro j hj hjI
  have hmem : j ∈ canceledIndices i k I := Finset.mem_sdiff.mpr ⟨hj,hjI⟩
  have hleft : wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j =
      v (((canceledIndices i k I).orderIsoOfFin rfl).symm ⟨j,hmem⟩) := by
    rw [← hv]
    simp [canceledPrimesAt,Finset.orderEmbOfFin]
  have hsame : wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j=
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j := by
    rw [← hI,canceledIndices_eq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  simpa only [dite_eq_left hmem] using And.intro hleft (hsame.symm.trans hleft)

/-- The raw published bound is unchanged when the finite actual family is
known injective in its recovered comparison data. -/
theorem actual_comparison_injective (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ {x t : ℝ} {H k K D r : ℕ} (I : Finset ℕ) (y S : ℝ) (Y U : ℕ → ℝ),
      y₀ ≤ y → FordComparisonParameters I.card y S D r Y U →
      L x H < m x → R x H < L x H →
      ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
      (∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2) →
      Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) →
      (∀ q ∈ Q, (suffixPreimage (chosenRemainder x H q.1.tail) k).totient=D) →
      (∀ q ∈ Q, (comparisonPairAt x H k I q).remainder.primeFactorsList.length ≤ K) →
      (∀ q ∈ Q, FordComparisonConditions I.card y S D r Y U (comparisonPairAt x H k I q)) →
      (Q.card : ℝ) ≤ (((R x H-k : ℕ) : ℝ)+1)^(D.primeFactorsList.length+K)*
        fordComparisonBound C I.card y S D r Y U := by
  obtain ⟨C,y₀,hC,hy₀,hbound⟩ := ford_comparison_with_recovery hford
  refine ⟨C,y₀,hC,hy₀,?_⟩
  intro x t H k K D r I y S Y U hy hparam hL hR Q hQ hinj hD hK hcond
  have hcard : (Q.image (comparisonEncoding x H k I)).card=Q.card := Finset.card_image_of_injOn hinj
  have hb := hbound I.card (R x H-k) K y S D r Y U hy hparam
    (Q.image (comparisonEncoding x H k I))
    (by intro z hz; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz; exact hcond q hq)
    (by intro z hz; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz; exact hK q hq)
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
