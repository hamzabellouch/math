import OAI.NumberTheory.DirichletL.Hecke.PrimeRay
import OAI.NumberTheory.DirichletL.Hecke.RowClosure
import OAI.NumberTheory.DirichletL.Hecke.Conjugation

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem identityClass_coprime {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    IsCoprime I M := by
  obtain ⟨hI,a,ha,u,hu,huH⟩ := hI
  rw [←ha]
  exact (IdealCharacter.isUnit_mk_iff_isCoprime M a).mp (hu ▸ u.isUnit)

omit [NeZero M] in
theorem identityClass_coprime_larger {I J : Ideal O}
    (hI : I∈RayQuotient.identityClass M H) (hMJ : M≤J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hI)]
  exact sup_le_sup_left hMJ I

omit [NeZero M] in
theorem identityClass_prime_good (m : O) (hmLam : λ₀∣m) (hMm : M≤Ideal.span {m})
    (P : Ideal O) [P.IsMaximal] (hP : P∈RayQuotient.identityClass M H) : λ₀∉P := by
  have hm : m∉P := (SixthPowerAverage.prime_coprime_span_iff P m).mp
    (identityClass_coprime_larger M H hP hMm)
  intro hLam
  obtain ⟨a,rfl⟩ := hmLam
  exact hm (P.mul_mem_right a hLam)

include hH in
theorem identityClass_principal_coeff {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    idealCoeff (HeckeRayFamily.character M 1) I=1 := by
  have hc := identityClass_coprime M H hI
  change RayQuotient.idealCharacter M H hH 1 I=1
  rw [RayQuotient.idealCharacter_one M H hH I,ite_eq_right hI.1,ite_eq_left hc]

include hH in
theorem exists_actual_prime_row (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (P : Ideal O) [P.IsMaximal] (hg : λ₀∉P),
      P∈RayQuotient.identityClass M H →
      idealCoeff χ P = starRingEnd ℂ
        (CompletedGauss.actualSextic P hg (Ideal.Quotient.mk P u)) := by
  obtain ⟨χ,hbound,hχ⟩ := exists_row_character_with_conductor (HeckeRayFamily.character M 1) m 1 u hm one_ne_zero hu hmLam hm2
  refine ⟨χ.inverse,hbound,?_⟩
  intro P _ hg hP
  have hc : IsCoprime P (Ideal.span {m}) := by
    rw [Ideal.isCoprime_iff_sup_eq] at ⊢
    apply top_unique
    rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hP)]
    exact sup_le_sup_left hMm P
  rw [idealCoeff_inverse_conj,idealCoeff_eq_row _ χ m 1 u hχ,
    identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,ite_eq_left hc,one_mul,
    idealRowHom_prime u P hg]

def canonicalPrimeAmplitude (u : O) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ P∈(HeckePrimeAnnular.annulusSet b D).filter
    (fun P => Prime P ∧ P∈RayQuotient.identityClass M H),
    starRingEnd ℂ (idealRowHom u P)*W ((P.absNorm : ℝ)/D)*
      (((P.absNorm : ℝ)/D : ℝ) : ℂ)^(z-1)

include hH in

theorem exists_amplitude_character (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (W : ℝ→ℂ) (b D : ℝ) (z : ℂ),
        canonicalPrimeAmplitude M H u W b D z =
          HeckePrimeRay.rayPrimePolynomial M H χ W b D (1-z.re) z.im := by
  obtain ⟨χ,hbound,hχ⟩ := exists_actual_prime_row M H hH m u hm hu hmLam hm2 hMm
  refine ⟨χ,hbound,?_⟩
  intro W b D z
  unfold canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := identityClass_prime_good M H m hmLam hMm P hclass
  have hc := hχ P hg hclass
  rw [←idealRowHom_prime u P hg] at hc
  rw [hc]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

end SevenEighths.HeckePrimeRow

end

end OAI
