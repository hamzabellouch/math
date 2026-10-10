import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiber
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialPhysicalSlots
open InverseInitialMarkedDictionary
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

theorem deletedBase_zero_unsupported (data:RowData)(I:Ideal O)(hI:¬Supported I) :
    idealCoeff (deletedBase data) I=0 := by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,baseCharacter_coeff,
    fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd I hI]
  split_ifs <;> rfl

theorem deletedBase_eq_of_ne_zero (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) :
    idealCoeff (deletedBase data) I=fixedBase data.η data.m data.f I := by
  unfold deletedBase excluded at hI ⊢
  rw [idealCoeff_excludePrimes,baseCharacter_coeff] at hI ⊢
  split_ifs with h
  · rfl
  · exact False.elim (hI (by simp [h]))

def deletedSelectedSource (data:RowData)(M:Ideal O)[NeZero M]
    (H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O) : ℂ :=
  ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
    (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
      idealCoeff (deletedBase data) (∏i,p i))*
    originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter Supported)
      (∏i,p i) (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
      (twistedProfile W σ freq) Z r (∑i,ell i) u

theorem deleted_physical_slots_norm_initial (data:RowData)(u:NonzeroElement)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(a b ell:ι→ℝ)(ζ:ι→ℂ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤bW)(hV:∀i x,V i x≠0→x∈Set.Icc (a i) (b i))
    (hlarge:∀i,((deletedBase data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖deletedSelectedSource data M H W V Z r σ freq bW b ell ζ u.val‖ := by
  let L:=fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A:=fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p:ι→Ideal O)(hp:p∈Fintype.piFinset L)(_ha:A p≠0):
      idealCoeff (deletedBase data) (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hd:=livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
    exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ _ hd.1.ne_zero
      (ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨p i,hd.1⟩
        ((hlarge i).trans_le hd.2.2.1))
  have he:=indexed_conjugate_mark_norm (Fintype.piFinset L) (fun p=>∏i,p i) A
    (idealCoeff (deletedBase data)).toMonoidHom
    ((data.character u).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)))
    u.val (actual_deleted_row data u) W Z r (∑i,ell i) σ freq hZ
    (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial ((data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset L,A p*star (idealRowHom u.val (∏i,p i)))‖=_
  rw [he]
  unfold deletedSelectedSource
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _ (deletedBase_zero_unsupported data)]
  rfl

theorem marked_fixed_deletion (data:RowData)(rows:Finset NonzeroElement)
    (W:ℝ→ℂ)(X σ t bW:ℝ)(hX:0<X)(hW:∀x,W x≠0→x≤bW)
    (mark:NonzeroElement→ℂ) :
    (∑u∈rows,‖polynomial (data.character u) true W X σ t*mark u‖^2)≤
      ((IdealMobiusDivisorSum.idealDivisors (∏P∈excluded data,P)).card:ℝ)*
      ∑j∈IdealMobiusDivisorSum.idealDivisors (∏P∈excluded data,P),∑u∈rows,
        ‖polynomial ((data.character u).excludePrimes (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data))) true W
          (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  simpa only [one_mul] using InverseInitialExcludedEnergy.marked_family rows data.character
    (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) W X σ t bW hX hW mark
    (fun _=>1) (fun _ _=>zero_le_one)

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
