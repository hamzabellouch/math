import OAI.NumberTheory.DirichletL.Hecke.PrimeNonprincipal
import OAI.NumberTheory.DirichletL.Hecke.PrimeScale
import OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckeDetectorPrimeFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure RowData (M : Ideal O) where
  m : O
  u : O
  m_ne_zero : m≠0
  u_ne_zero : u≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m
  modulus_le : M≤Ideal.span {m}

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def RowData.base (data : RowData M) : Character :=
  Classical.choose (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)

theorem RowData.base_spec (data : RowData M) (n : O) :
    elementCoeff (data.base M) n=
      rowTwist (elementHom (HeckeRayFamily.character M 1)) data.m 1 data.u n :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).2 n

theorem RowData.base_conductor (data : RowData M) :
    (data.base M).modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) data.m 1 data.u :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).1

def RowData.character (data : RowData M) : Character := (data.base M).inverse

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH in
theorem RowData.coefficient_on_ray (data : RowData M) (P : Ideal O) [P.IsMaximal]
    (hg : λ₀∉P) (hP : P∈RayQuotient.identityClass M H) :
    idealCoeff (data.character M) P=starRingEnd ℂ (idealRowHom data.u P) := by
  have hc := HeckePrimeRow.identityClass_coprime_larger M H hP data.modulus_le
  rw [RowData.character,idealCoeff_inverse_conj,
    idealCoeff_eq_row _ (data.base M) data.m 1 data.u (data.base_spec M),
    HeckePrimeRow.identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask data.m P hg,ite_eq_left hc,one_mul]

include hH in
theorem RowData.amplitude_eq (data : RowData M) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H data.m data.lambda_dvd data.modulus_le P hclass
  rw [data.coefficient_on_ray M H hH P hg hclass]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

theorem RowData.twisted_conductor (data : RowData M) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm := by
  apply HeckePrimeScale.twisted_row_modulus_bound M H hH (data.character M) data.m data.u
  exact data.base_conductor M

theorem RowData.twisted_nonprincipal (data : RowData M)
    (unit : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : data.u=(unit : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  exact HeckePrimeNonprincipal.fixed_ray_twisted_nonprincipal M H hH (data.base M)
    data.m 1 data.u (data.base_spec M) data.lambda_dvd data.two_dvd unit a b r hr hpr
    (by simpa using hx) P J hg hchar hJ hc hc6 hsplit hcop θ

structure Ramification (data : RowData M) where
  unit : Oˣ
  lambda_power : ℕ
  two_power : ℕ
  remaining : O
  supported : CanonicalQuadraticSieve.Supported (Ideal.span {remaining})
  primary : λ₀^2∣remaining-1
  decomposition : data.u=(unit : O)*λ₀^lambda_power*(2 : O)^two_power*remaining
  prime : Ideal O
  rest : Ideal O
  maximal : prime.IsMaximal
  prime_good : λ₀∉prime
  odd : ringChar (O ⧸ prime)≠2
  rest_supported : CanonicalQuadraticSieve.Supported rest
  multiplicity : ℕ
  multiplicity_pos : 1≤multiplicity
  not_sixfold : ¬6∣multiplicity
  split : Ideal.span {remaining}=prime^multiplicity*rest
  coprime : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*rest) (prime^multiplicity)

theorem Ramification.nonprincipal {data : RowData M} (cert : Ramification M data)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  let := cert.maximal
  exact data.twisted_nonprincipal M H hH cert.unit cert.lambda_power cert.two_power
    cert.remaining cert.supported cert.primary cert.decomposition cert.prime cert.rest cert.prime_good
    cert.odd cert.rest_supported cert.multiplicity_pos cert.not_sixfold cert.split cert.coprime θ

end SevenEighths.HeckeDetectorPrimeFamily

end

end OAI
