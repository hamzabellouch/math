import Mathlib
import OAI.NumberTheory.PrimePackets.CosetMeromorphic
import OAI.NumberTheory.PrimePackets.MonomialArtin

namespace OAI

noncomputable section
open Module Filter Topology
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.ArtinInduction
open GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

 

def monomialRationalEuler (L : IntermediateField F E)
    (χ : (E ≃ₐ[L] E) →* ℂˣ) (N : ℕ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if p.val ∣ N then 1 else
    ∏ P : idealsOverPrime F p.val,
      let ρ := Representation.coind L.fixingSubgroup.subtype
        (unitCharacterRep (χ.comp (IntermediateField.fixingSubgroupEquiv L).toMonoidHom))
      (LinearMap.det (LinearMap.id - (Ideal.absNorm P.val : ℂ)^(-s) •
        ρ (primeFrobenius F E (rationalPrimeSpectrum F p P))))⁻¹

lemma monomialRationalEuler_good (L : IntermediateField F E)
    (χ : (E ≃ₐ[L] E) →* ℂˣ) {N : ℕ}
    (hD : (NumberField.discr E).natAbs ∣ N)
    (p : Nat.Primes) (hp : ¬ p.val ∣ N) {s : ℂ} (hs : 1 < s.re) :
    monomialRationalEuler F E L χ N p s =
      ∏ R : idealsOverPrime L p.val,
        (1 - ArtinSeries.idealTerm χ N hs R.val)⁻¹ := by
  have hpC : p.val.Coprime N := p.property.coprime_iff_not_dvd.mpr hp
  have hpD : p.val.Coprime (NumberField.discr E).natAbs := hpC.of_dvd_right hD
  let (P : idealsOverPrime F p.val) : P.val.IsPrime :=
    ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).1
  let (P : idealsOverPrime F p.val) : Fintype (Ideal.primesOver P.val (𝓞 L)) :=
    (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  rw [monomialRationalEuler, ite_eq_right hp,
    ← (primeIdealTowerEquiv F L p.val p.property.ne_zero).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro P _
  let PP := rationalPrimeSpectrum F p P
  let Q := primeAbove F E PP
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E PP)
  let : Q.val.LiesOver PP.asIdeal := Q.property.2
  let : Algebra.IsUnramifiedAt (𝓞 F) Q.val :=
    unramified_of_absDiscr_not_mem F E PP.asIdeal Q.val Q.property.2.over.symm
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast
        ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).2)
  refine (actual_monomial_artin_localEuler F E L PP Q.val
    (primeFrobenius F E PP) (primeFrobenius_spec F E PP) χ s).trans ?_
  apply Finset.prod_congr rfl
  intro R _
  let RP : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    ⟨R.val, R.property.1, Ideal.ne_bot_of_mem_primesOver PP.ne_bot R.property⟩
  have hpR : (p.val : 𝓞 L) ∈ R.val := by
    have hm : algebraMap (𝓞 F) (𝓞 L) (p.val : 𝓞 F) ∈ R.val := by
      change (p.val : 𝓞 F) ∈ R.val.under (𝓞 F)
      rw [← R.property.2.over]
      exact ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).2
    simpa only [map_natCast] using hm
  have hc : IsCoprime R.val (ThetaConstruction.rationalModulusIdeal (𝓞 L) N) := by
    apply Ideal.isCoprime_iff_codisjoint.mpr
    apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hpR) le_rfl
    exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hpC.cast).codisjoint
  have he : ArtinSeries.idealTerm χ N hs R.val =
      (χ (primeFrobenius L E RP) : ℂ) * (Ideal.absNorm R.val : ℂ)^(-s) := by
    rw [ArtinSeries.idealTerm_apply]
    change artinCoefficient L E χ N RP.asIdeal * _ = _
    rw [artinCoefficient, dite_eq_left RP.ne_bot, ite_eq_left hc, idealHom_prime]
  rw [he]

 

theorem actual_monomial_artin_factorization (L : IntermediateField F E)
    (χ : (E ≃ₐ[L] E) →* ℂˣ) (N : ℕ)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => monomialRationalEuler F E L χ N p s)
      (artinDirichlet L E χ N s) := by
  apply (ArtinSeries.dirichlet_hasProd χ N hs).congr_fun
  intro p
  by_cases hp : p.val ∣ N
  · rw [ArtinSeries.local_euler_bad L E χ p hp hs]
    simp only [monomialRationalEuler, ite_eq_left hp]
  · exact monomialRationalEuler_good F E L χ hD p hp hs

end PrimeDegreePackets.ArtinInduction
end

end OAI
