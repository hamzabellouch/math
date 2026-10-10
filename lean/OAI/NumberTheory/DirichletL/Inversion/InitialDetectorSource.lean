import OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
import OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
import OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
import OAI.NumberTheory.DirichletL.Detector.RayPoolGood

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace SevenEighths.InverseInitialDetectorSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open InverseInitialRawDictionary InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

def baseCharacter (data : RowData) : Character := data.character ⟨1,one_ne_zero⟩

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (baseCharacter data) I=fixedBase data.η data.m data.f I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η (baseCharacter data) data.m data.f 1
    (data.character_spec ⟨1,one_ne_zero⟩),mul_one]
  rfl

theorem base_nonzero_prime (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    fixedBase data.η data.m data.f P≠0 := by
  rw [←baseCharacter_coeff]
  exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hN)

theorem character_eq_initial (data : RowData) (u : NonzeroElement)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial (data.character u) true W (Z^r) σ freq=
      originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u.val :=
  canonical_inverse_eq_supported_initial data.η (data.character u) data.m data.f u.val
    data.lambda_dvd data.two_dvd (data.character_spec u) W Z r σ freq b hZ hW

theorem oriented_character_norm_initial (data : RowData) (u : NonzeroElement)
    (χ : Character) (reverse : Bool)
    (hc : ∀I,idealCoeff χ I=if reverse then conj (idealCoeff (data.character u) I)
      else idealCoeff (data.character u) I)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    ‖polynomial χ true W (Z^r) σ freq‖=
      ‖originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile (orientedProfile reverse W) σ (orientedFrequency reverse freq))
        Z r 0 u.val‖ := by
  rw [norm_of_oriented_coefficients χ (data.character u) reverse hc true W (Z^r) σ freq
    (Real.rpow_pos_of_pos hZ r)]
  rw [character_eq_initial data u (orientedProfile reverse W) Z r σ
    (orientedFrequency reverse freq) b hZ]
  intro x hx
  apply hW x
  intro hz
  exact hx (by cases reverse <;> simp [orientedProfile,hz])

def primeProfile (V : ℝ→ℂ) (D : ℝ) (ζ : ℂ) (P : Ideal O) : ℂ :=
  V ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(ζ-1)

theorem physical_slot_norm_initial (data : RowData) (u : NonzeroElement)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (W V : ℝ→ℂ) (Z r ell σ freq b bslot a : ℝ) (ζ : ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) (hV : ∀x,V x≠0 → a≤x)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<a*Z^ell) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ‖=
    ‖∑P∈(HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
        (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H),
      (star (primeProfile V (Z^ell) ζ P)/fixedBase data.η data.m data.f P)*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
          P (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ freq) Z r ell u.val‖ := by
  let Pset := (HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)
  have hc := finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW
  have hbase (P : Ideal O) (hp : P∈Pset) (ha : primeProfile V (Z^ell) ζ P≠0) :
      fixedBase data.η data.m data.f P≠0 := by
    apply base_nonzero_prime data P (Finset.mem_filter.mp hp).2.1
    have hv : V ((P.absNorm:ℝ)/Z^ell)≠0 := by
      intro hz
      exact ha (by simp [primeProfile,hz])
    exact hlarge.trans_le ((le_div_iff₀ (Real.rpow_pos_of_pos hZ ell)).mp (hV _ hv))
  have he := inverse_times_conjugate_row_mark_norm (fixedBase data.η data.m data.f)
    (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r ell σ freq hZ (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊) Pset
    (primeProfile V (Z^ell) ζ) hbase hc
  have hp : HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈Pset,
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u.val P) := by
    unfold HeckePrimeRow.canonicalPrimeAmplitude
    rw [normalization_eq Z ell hZ]
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    change star (CanonicalRowCompletion.idealRowHom u.val P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u.val P)
    ring
  rw [hp,←mul_assoc,he]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

end SevenEighths.InverseInitialDetectorSource

end

end OAI
