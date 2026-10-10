import OAI.NumberTheory.TwoPoint.Bounds.PrimeWordEncoding

namespace OAI

/-! Every prime used by a numerical encoding lies in its declared finite pools. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem PrimeWordEncoding.divisor_support_subset {R T : ℕ} {P Q : Finset ℕ}
    (e : PrimeWordEncoding R T P Q)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) :
    wordDivisorPrimeSupport e.decode ⊆ P ∪ Q := by
  let c := e.2.1
  let value := joinCoordinates c.tupleClasses
    (fun z => (e.2.2.1 z).val) (fun z => (e.2.2.2 z).val)
  have hv (z : c.usedClasses) : value z ∈ P ∪ Q := by
    by_cases hz : z ∈ c.tupleClasses
    · exact mem_union_left _ (by simpa only [value, joinCoordinates, hz, dite_true]
        using (e.2.2.1 ⟨z, hz⟩).property)
    · exact mem_union_right _ (by simpa only [value, joinCoordinates, hz, dite_false]
        using (e.2.2.2 ⟨z, hz⟩).property)
  have hpv (z : c.usedClasses) : (value z).Prime := by
    rcases mem_union.mp (hv z) with hz | hz
    · exact hP _ hz
    · exact hQ _ hz
  intro q hq
  have hm : ∃ i : Fin R, q ∈
      ((c.primeData value).factor i true * (c.primeData value).factor i false).primeFactors := by
    change q ∈ wordDivisorPrimeSupport (c.primeData value).word at hq
    simpa only [wordDivisorPrimeSupport, PrimeSlotData.word, mem_biUnion,
      List.mem_toFinset, List.mem_ofFn, exists_exists_eq_and] using hq
  obtain ⟨i, hi⟩ := hm
  have hprime := (Nat.mem_primeFactors.mp hi).1
  have hdvd := (Nat.mem_primeFactors.mp hi).2.1
  have hf (b : Bool) (hd : q ∣ (c.primeData value).factor i b) : q ∈ P ∪ Q := by
    obtain ⟨j, _, hj⟩ := (hprime.prime.dvd_finsetProd_iff
      (c.primeData value).prime).mp hd
    have he : q = value (c.classAt j) :=
      (Nat.prime_dvd_prime_iff_eq hprime (hpv (c.classAt j))).mp hj
    rw [he]
    exact hv _
  rcases hprime.dvd_mul.mp hdvd with hd | hd
  · exact hf true hd
  · exact hf false hd

end TwoPointCorrelations

end OAI
