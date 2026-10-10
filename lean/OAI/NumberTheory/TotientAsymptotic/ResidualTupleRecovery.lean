import OAI.NumberTheory.TotientAsymptotic.PrefixSize
import OAI.NumberTheory.TotientAsymptotic.TupleRecovery

namespace OAI

/-! The exact tuple data hidden in a comparison residual, on either side of the prefix cut. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def residualTupleData {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) (k : ℕ) :
    PrefixDatum (R x H-k) where
  primes := fun j => remainderPrime η (k+j.val+1)
  d := if k ≤ R x H then (remainderTail x H η).totient else (suffixPreimage η k).totient

lemma prod_after_cut {M : Type*} [CommMonoid M] {k R : ℕ} (hk : k ≤ R) (f : ℕ → M) :
    (∏ j : Fin (R-k), f (k+j.val+1)) = ∏ r ∈ Finset.Icc (k+1) R, f r := by
  apply Finset.prod_bij (fun j _ => k+j.val+1)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩
  · intro j _ l _ h
    apply Fin.ext
    omega
  · intro r hr
    have hh := Finset.mem_Icc.mp hr
    refine ⟨⟨r-k-1,by omega⟩,Finset.mem_univ _,?_⟩
    simp only
    omega
  · intro j _
    rfl

lemma residualTupleData_denominator {x : ℝ} {H k : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x) (hR : R x H < L x H) :
    prefixDenominator (residualTupleData η k) = (suffixPreimage η k).totient := by
  by_cases hk : k ≤ R x H
  · simp only [prefixDenominator,residualTupleData,ite_eq_left hk]
    rw [prod_after_cut hk (fun r => remainderPrime η r-1),← suffixPreimage_at_R η]
    exact (basic_suffix_totient_split hη hL hk hR).symm
  · have hzero : R x H-k=0 := by omega
    simp only [prefixDenominator,residualTupleData,ite_eq_right hk]
    have he : (∏ j : Fin (R x H-k), (remainderPrime η (k+j.val+1)-1))=1 := by
      rw [hzero]
      simp
    rw [he,mul_one]

lemma residualTupleData_primes {x : ℝ} {H k : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hRL : R x H ≤ L x H) :
    ∀ j, 1 ≤ (residualTupleData η k).primes j := by
  intro j
  have hj := j.isLt
  exact (hη.2.1 (k+j.val+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).1.one_lt.le

/-- Different full witnesses can give the same residual tuple. Counting its
distinct values uses only the number of prime occurrences of the residual. -/
theorem residual_tuple_data_card {x : ℝ} {H k D : ℕ}
    (S : Finset (RemainderDatum (L x H))) (hD : 0 < D)
    (hL : L x H < m x) (hR : R x H < L x H)
    (hS : ∀ η ∈ S, IsBasicRemainder x H η)
    (hval : ∀ η ∈ S, (suffixPreimage η k).totient=D) :
    (S.image (fun η => residualTupleData η k)).card ≤
      (R x H-k+1)^D.primeFactorsList.length := by
  apply prefixData_card_le hD
  · intro ζ hζ
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hζ
    exact residualTupleData_primes (hS η hη) hR.le
  · intro ζ hζ
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hζ
    exact (residualTupleData_denominator (hS η hη) hL hR).trans (hval η hη)

/-- The known comparison primes and the residual tuple determine the
original prefix datum, including when the comparison cut is beyond `R`. -/
theorem prefix_recovered_from_residual {x : ℝ} {H k : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hξ : IsBasicRemainder x H ξ)
    (hL : L x H < m x) (hkL : k < L x H)
    (hknown : ∀ r ∈ Finset.Icc 1 k, remainderPrime η r=remainderPrime ξ r)
    (hdata : residualTupleData η k=residualTupleData ξ k) :
    prefixOfRemainder x H η=prefixOfRemainder x H ξ := by
  have hprimes := congrArg PrefixDatum.primes hdata
  have hd := congrArg PrefixDatum.d hdata
  have hp : (prefixOfRemainder x H η).primes=(prefixOfRemainder x H ξ).primes := by
    funext j
    change remainderPrime η (j.val+1)=remainderPrime ξ (j.val+1)
    by_cases hjk : j.val+1 ≤ k
    · exact hknown _ (Finset.mem_Icc.mpr ⟨by omega,hjk⟩)
    · have hj := j.isLt
      let l : Fin (R x H-k) := ⟨j.val-k,by omega⟩
      have hh := congrFun hprimes l
      change remainderPrime η (k+l.val+1)=remainderPrime ξ (k+l.val+1) at hh
      have he : k+l.val+1=j.val+1 := by dsimp [l]; omega
      simpa only [he] using hh
  have htail : (prefixOfRemainder x H η).d=(prefixOfRemainder x H ξ).d := by
    by_cases hk : k ≤ R x H
    · change (remainderTail x H η).totient=(remainderTail x H ξ).totient
      simpa only [residualTupleData,ite_eq_left hk] using hd
    · have hD : (suffixPreimage η k).totient=(suffixPreimage ξ k).totient := by
        simpa only [residualTupleData,ite_eq_right hk] using hd
      change (remainderTail x H η).totient=(remainderTail x H ξ).totient
      rw [← suffixPreimage_at_R η,← suffixPreimage_at_R ξ,
        basic_suffix_totient_split hη hL (by omega : R x H ≤ k) hkL,
        basic_suffix_totient_split hξ hL (by omega : R x H ≤ k) hkL,hD]
      congr 1
      apply Finset.prod_congr rfl
      intro r hr
      rw [hknown r (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hr).1; omega,
        (Finset.mem_Icc.mp hr).2⟩)]
  exact congrArg₂ PrefixDatum.mk hp htail

end TotientAsymptotic

end

end OAI
