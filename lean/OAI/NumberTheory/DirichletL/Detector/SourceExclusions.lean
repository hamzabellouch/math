import OAI.NumberTheory.DirichletL.Detector.HighLFactorization

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_prime_supported (S : Finset Id) (hbad : fixedBadPrimes⊆S)
    (P : PrimeIdeal) (hP : P.val∉S) : Supported P.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  refine ⟨P.property.ne_zero,?_⟩
  intro Q hQ
  have heq : Q=P.val := by
    simpa only [normalizedFactors_irreducible P.property.irreducible,normalize_eq,
      Multiset.mem_singleton] using hQ
  subst Q
  exact (prime_good_iff_not_bad P.val).mpr (fun h=>hP (hbad h))

structure SourceExclusions (S : Finset Id) : Prop where
  prime : ∀P∈S,Prime P
  bad : fixedBadPrimes⊆S
  tail : CorrectionTail S

theorem exists_source_exclusions (S₀ : Finset Id) (hp : ∀P∈S₀,Prime P)
    (hbad : fixedBadPrimes⊆S₀) :
    ∃S : Finset Id,S₀⊆S ∧ SourceExclusions S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,?_⟩
  constructor
  · intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  · exact hbad.trans Finset.subset_union_left
  · apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z :=
  principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad) hS.tail η x w z hx hw hz

theorem source_globalCorrection_principal (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x :=
  globalClosedCorrection_principal η S (outside_prime_supported S hS.bad) x

end SevenEighths.ProbePhysical
end

end OAI
