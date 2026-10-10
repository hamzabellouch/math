import OAI.NumberTheory.DirichletL.PrimeRows.Continuation

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow) : Finset {P : PrimeIdeal // P.val∉S} :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).subtype (fun P => P.val∉S)

theorem mem_ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow)
    (P : {P : PrimeIdeal // P.val∉S}) : P∈ramifiedIndices S u ↔ P.val.val∣Ideal.span {u.val} := by
  simp only [ramifiedIndices,Finset.mem_subtype,SmoothMobiusCorrection.mem_primeSet,
    IdealMobiusDivisorSum.primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (show (Ideal.span {u.val}:Ideal O)≠0 from Ideal.span_singleton_eq_bot.not.mpr u.property.1),
    P.val.property,true_and]

def ramifiedFactor (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (P : {P : PrimeIdeal // P.val∉S}) (x w z : ℂ) : ℂ :=
  if P.val.val∣Ideal.span {u.val} then
    ramifiedCorrection η u P.val (outside_prime_supported S hS.bad P.val P.property) x w z else 1

theorem ramifiedFactor_hasProd (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    HasProd (fun P =>ramifiedFactor S hS η u P x w z) (ramifiedProduct S hS η u x w z) := by
  have he : (∏ P∈ramifiedIndices S u,ramifiedFactor S hS η u P x w z)=
      ramifiedProduct S hS η u x w z := by
    unfold ramifiedProduct
    apply Finset.prod_bij (fun P hP =>
      (⟨P.val,Finset.mem_filter.mpr ⟨Finset.mem_subtype.mp hP,P.property⟩⟩ : ramifiedPrimes S u))
    · intro P hP; exact Finset.mem_attach _ _
    · intro P hP Q hQ heq
      exact Subtype.ext (congrArg (fun R : ramifiedPrimes S u => R.val) heq)
    · intro P hP
      refine ⟨⟨P.val,(Finset.mem_filter.mp P.property).2⟩,?_,?_⟩
      · exact Finset.mem_subtype.mpr (Finset.mem_filter.mp P.property).1
      · rfl
    · intro P hP
      simp only [ramifiedFactor,ite_eq_left ((mem_ramifiedIndices S u P).mp hP)]
  rw [←he]
  apply hasProd_prod_of_ne_finset_one
  intro P hP
  exact ite_eq_right (fun hd => hP ((mem_ramifiedIndices S u P).mpr hd))

theorem supported_prime_coprime (P : PrimeIdeal) (hs : Supported P.val) (u : O)
    (hn : ¬P.val∣Ideal.span {u}) : IsCoprime P.val (Ideal.span {u}) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have he : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  have hnot : ¬p∣u := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←he,Ideal.span_singleton_le_span_singleton]
    exact hd
  rw [←he,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr hnot

theorem continuedCorrection_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCorrection S hS η u x w z=globalCorrection S η u x w z := by
  have hr := ramifiedFactor_hasProd S hS η u x w z
  have hu := (unramifiedProduct_multipliable S hS.tail η u x w z
    (by linarith) (by linarith) (by linarith)).hasProd
  have he := hr.mul hu
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ramifiedFactor S hS η u P x w z*unramifiedFactor η u P.val x w z=
        localCorrection η u P.val x w z := by
    have hs := outside_prime_supported S hS.bad P.val P.property
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simp only [ramifiedFactor,unramifiedFactor,ite_eq_left h,mul_one]
      exact (localCorrection_eq_ramified η u P.val hs h x w z hx hw hz).symm
    · simp only [ramifiedFactor,unramifiedFactor,ite_eq_right h,one_mul]
      exact (localCorrection_unramified_ideal η u P.val hs
        (supported_prime_coprime P.val hs u.val h) x w z hx hw hz).symm
  have hh : HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (continuedCorrection S hS η u x w z) := by
    simpa only [hlocal,continuedCorrection,unramifiedProduct] using he
  exact hh.tprod_eq.symm

theorem high_L_factorization_continued (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w /
        LFunction ((targetRow η u).excludePrimes S hS.prime) x*continuedCorrection S hS η u x w z := by
  rw [continuedCorrection_eq_initial S hS η u x w z hx hw hz]
  exact high_L_factorization S hS.prime hS.bad η u x w z hx hw hz

end SevenEighths.ProbeHighRowFamily

end

end OAI
