import OAI.NumberTheory.CubicMoment.Estimates.PrimeIntervalGeometry

namespace OAI

/-! Exact selection of a largest prime, with a fixed injective tie code.
This is an unordered selection: inserting it into a finite sum introduces
no factor depending on the number of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeTieCode (p : Eisenstein) : ℕ :=
  Encodable.encode (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p)

lemma primeTieCode_injective : Function.Injective primeTieCode := by
  intro p q h
  have hi : Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p =
      Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q := Encodable.encode_injective h
  have hr := Function.rightInverse_invFun ofCoords_surjective
  calc
    p = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).2 := (hr p).symm
    _ = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).2 := by rw [hi]
    _ = q := hr q

lemma exists_largestPrime (code : Eisenstein → ℕ) (s : Finset Eisenstein)
    (hs : s.Nonempty) : ∃ p ∈ s, largestPrimePredicate code s p := by
  obtain ⟨q,hq,hnq⟩ := Finset.exists_mem_eq_sup s hs normNat
  let T := s.filter (fun p => normNat p = s.sup normNat)
  have hqT : q ∈ T := Finset.mem_filter.mpr ⟨hq,hnq.symm⟩
  obtain ⟨p,hp,hcp⟩ := Finset.exists_mem_eq_sup T ⟨q,hqT⟩ code
  have hpn := (Finset.mem_filter.mp hp).2
  refine ⟨p,(Finset.mem_filter.mp hp).1,?_⟩
  intro r hr
  have hrn : normNat r ≤ normNat p := (Finset.le_sup (f := normNat) hr).trans_eq hpn.symm
  by_cases hlt : normNat r < normNat p
  · exact Or.inl hlt
  · have he : normNat r = normNat p := le_antisymm hrn (le_of_not_gt hlt)
    have hrT : r ∈ T := Finset.mem_filter.mpr ⟨hr,he.trans hpn⟩
    exact Or.inr ⟨he,hcp ▸ Finset.le_sup (f := code) hrT⟩

lemma largestPrime_unique {code : Eisenstein → ℕ} (hc : Function.Injective code)
    {s : Finset Eisenstein} {p q : Eisenstein} (hp : p ∈ s) (hq : q ∈ s)
    (hpl : largestPrimePredicate code s p) (hql : largestPrimePredicate code s q) : p = q := by
  rcases hpl q hq with hlt | he
  · rcases hql p hp with hlt' | he'
    · omega
    · omega
  · rcases hql p hp with hlt' | he'
    · omega
    · exact hc (le_antisymm he'.2 he.2)

def selectedLargestPrime (s : Finset Eisenstein) (hs : s.Nonempty) : Eisenstein :=
  Classical.choose (exists_largestPrime primeTieCode s hs)

lemma selectedLargestPrime_spec (s : Finset Eisenstein) (hs : s.Nonempty) :
    selectedLargestPrime s hs ∈ s ∧
      largestPrimePredicate primeTieCode s (selectedLargestPrime s hs) :=
  Classical.choose_spec (exists_largestPrime primeTieCode s hs)

lemma selectedLargestPrime_norm (s : Finset Eisenstein) (hs : s.Nonempty) :
    normNat (selectedLargestPrime s hs) = s.sup normNat := by
  have hp := selectedLargestPrime_spec s hs
  apply le_antisymm (Finset.le_sup (f := normNat) hp.1)
  apply Finset.sup_le
  intro q hq
  rcases hp.2 q hq with hlt | he
  · exact hlt.le
  · exact he.1.le

lemma selectedLargestPrime_large {s : Finset Eisenstein} (hs : s.Nonempty)
    {Y : ℝ} (hY : ∃ q ∈ s, Y < norm q) : Y < norm (selectedLargestPrime s hs) := by
  obtain ⟨q,hq,hqY⟩ := hY
  apply hqY.trans_le
  rw [←normNat_cast,←normNat_cast,selectedLargestPrime_norm]
  exact_mod_cast (Finset.le_sup (f := normNat) hq)

lemma selectedLargestPrime_product_split (s : Finset Eisenstein) (hs : s.Nonempty) :
    selectedLargestPrime s hs*(∏ q ∈ s.erase (selectedLargestPrime s hs), q) =
      ∏ q ∈ s, q := by
  simpa only [mul_comm] using Finset.prod_erase_mul s (fun q => q)
    (selectedLargestPrime_spec s hs).1

/-- The actual largest prime of a squarefree primary element can be
removed once, leaving a primary squarefree factor coprime to it. -/
theorem primary_largest_prime_split {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) (hne : (primaryPrimeFactors n).Nonempty) :
    ∃ p c : Eisenstein, primaryPrime p ∧ primary c ∧ Squarefree c ∧
      ¬p ∣ c ∧ p*c = n ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors c) p ∧
      normNat p = (primaryPrimeFactors n).sup normNat := by
  let p := selectedLargestPrime (primaryPrimeFactors n) hne
  let U := (primaryPrimeFactors n).erase p
  let c := ∏ q ∈ U, q
  have hp := selectedLargestPrime_spec (primaryPrimeFactors n) hne
  have hpP : primaryPrime p := (primaryPrimeFactor_spec hn hp.1).1
  have hU (q : Eisenstein) (hq : q ∈ U) : primaryPrime q :=
    (primaryPrimeFactor_spec hn (Finset.mem_of_mem_erase hq)).1
  have hc : primary c := primary_finset_prod U (fun q => q) (fun q hq => (hU q hq).1)
  have hf : primaryPrimeFactors c = U := primaryPrimeFactors_finset_prod U hU
  have hpc : ¬p ∣ c := by
    intro hd
    have hm := (primaryPrime_mem_factors_iff hc).mpr ⟨hpP,hd⟩
    rw [hf] at hm
    exact (Finset.mem_erase.mp hm).1 rfl
  refine ⟨p,c,hpP,hc,primaryPrime_product_squarefree U hU,hpc,?_,?_,?_⟩
  · exact (selectedLargestPrime_product_split (primaryPrimeFactors n) hne).trans
      (primaryPrimeFactors_prod hn hs)
  · rw [hf]
    exact fun q hq => hp.2 q (Finset.mem_of_mem_erase hq)
  · exact selectedLargestPrime_norm (primaryPrimeFactors n) hne

lemma largestPrimePredicate_erase (code : Eisenstein → ℕ)
    (s : Finset Eisenstein) (p : Eisenstein) :
    largestPrimePredicate code (s.erase p) p ↔ largestPrimePredicate code s p := by
  constructor
  · intro h q hq
    by_cases hqp : q = p
    · subst q
      exact Or.inr ⟨rfl,le_rfl⟩
    · exact h q (Finset.mem_erase.mpr ⟨hqp,hq⟩)
  · intro h q hq
    exact h q (Finset.mem_of_mem_erase hq)

theorem sum_largestPrime_selected (s : Finset Eisenstein) (hs : s.Nonempty)
    (F : Eisenstein → ℂ) :
    (∑ p ∈ s with largestPrimePredicate primeTieCode (s.erase p) p, F p) =
      F (selectedLargestPrime s hs) := by
  have hspec := selectedLargestPrime_spec s hs
  have hset : s.filter (fun p => largestPrimePredicate primeTieCode (s.erase p) p) =
      {selectedLargestPrime s hs} := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hp,hpred⟩
      exact largestPrime_unique primeTieCode_injective hp hspec.1
        ((largestPrimePredicate_erase primeTieCode s p).mp hpred) hspec.2
    · intro he
      subst p
      exact ⟨hspec.1,(largestPrimePredicate_erase _ _ _).mpr hspec.2⟩
  rw [hset,Finset.sum_singleton]

end CubicFirstMoment

end

end OAI
