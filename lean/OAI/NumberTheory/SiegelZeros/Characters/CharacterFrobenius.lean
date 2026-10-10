import OAI.NumberTheory.SiegelZeros.Determinants.IntegralGaussReduction
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ResidueField
import OAI.NumberTheory.SiegelZeros.Structure.SignedDiscriminant

namespace OAI

namespace SiegelZeros


namespace Awei.W39
open SiegelZerosAwei.W09
open scoped NumberField

theorem character_legendre_signedConductor_of_residue
    {q : ℕ} [NeZero q] {F : Type*} [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (hpq : ¬ p ∣ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (ρ : 𝓞 (complexCyclotomicField q) →+* F) :
    χ (p : ZMod q) = (legendreSym p (signedConductor χ) : ℂ) := by
  exact character_legendre_of_signed_gaussSum_sq p hp hpq χ hquad
    (residueAddChar ρ) (signedConductor χ) (signedConductor_natAbs χ)
    (residueGaussSum_sq ρ χ hprim hquad)

theorem character_legendre_radicand_of_residue
    {q : ℕ} [NeZero q] {F : Type*} [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (hpq : ¬ p ∣ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (ρ : 𝓞 (complexCyclotomicField q) →+* F)
    (d t : ℤ) (hD : signedConductor χ = d * t ^ 2) :
    χ (p : ZMod q) = (legendreSym p d : ℂ) := by
  have hgood : (signedConductor χ : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_not_dvd_natAbs p _ (by rwa [signedConductor_natAbs χ])
  rw [character_legendre_signedConductor_of_residue p hp hpq χ hprim hquad ρ,
    legendre_remove_square_factor p _ d t hD hgood]

end Awei.W39



namespace Awei.W39
open SiegelZerosAwei.W09 SiegelZerosAwei.W38
open scoped NumberField

theorem character_legendre_signedConductor
    {q : ℕ} [NeZero q] (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hpq : ¬ p ∣ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) :
    χ (p : ZMod q) = (legendreSym p (signedConductor χ) : ℂ) := by
  let cyclotomicExtension := complexCyclotomicField_isCyclotomic (q := q)
  let finiteDimensional : FiniteDimensional ℚ (complexCyclotomicField q) :=
    IsCyclotomicExtension.finiteDimensional {q} ℚ (complexCyclotomicField q)
  let numberField : NumberField (complexCyclotomicField q) := ⟨⟩
  exact character_legendre_signedConductor_of_residue p hp hpq χ hprim hquad
    (primeReduction (complexCyclotomicField q) p)

theorem character_legendre_radicand
    {q : ℕ} [NeZero q] (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hpq : ¬ p ∣ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (d k : ℤ) (hD : signedConductor χ = k ^ 2 * d) :
    χ (p : ZMod q) = (legendreSym p d : ℂ) := by
  have hgood : (signedConductor χ : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_not_dvd_natAbs p _ (by rwa [signedConductor_natAbs χ])
  rw [character_legendre_signedConductor p hp hpq χ hprim hquad,
    legendre_remove_square_factor p _ d k (by simpa only [mul_comm] using hD) hgood]

theorem goodPrime_legendre_radicand
    {q : ℕ} [NeZero q] (H p : ℕ) [Fact p.Prime]
    (hH : 2 ≤ H) (hpH : H < p) (hpq : ¬ p ∣ 2 * q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hchi : χ (p : ZMod q) = -1)
    (d k : ℤ) (hD : signedConductor χ = k ^ 2 * d) :
    legendreSym p d = -1 := by
  have hp2 : p ≠ 2 := ne_of_gt (lt_of_le_of_lt hH hpH)
  have hpq' : ¬ p ∣ q := fun h => hpq (dvd_mul_of_dvd_right h 2)
  have he := character_legendre_radicand p hp2 hpq' χ hprim hquad d k hD
  apply Int.cast_injective (α := ℂ)
  simpa only [Int.cast_neg, Int.cast_one] using he.symm.trans hchi

theorem actual_character_frobenius_two_conjugates
    {q : ℕ} [NeZero q] {R : Type*} [CommRing R]
    (H p : ℕ) [Fact p.Prime] (hH : 2 ≤ H) (hpH : H < p) (hpq : ¬ p ∣ 2 * q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hchi : χ (p : ZMod q) = -1)
    (d k : ℤ) (hD : signedConductor χ = k ^ 2 * d)
    (a b : R) (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = 2) :
    (∀ n : Fin 4 → ℤ, (p : R) ∣ theta a b n ^ p - theta (-a) b n) ∨
    (∀ n : Fin 4 → ℤ, (p : R) ∣ theta a b n ^ p - theta (-a) (-b) n) := by
  exact theta_frobenius_two_conjugates p (ne_of_gt (lt_of_le_of_lt hH hpH))
    a b d ha hb (goodPrime_legendre_radicand H p hH hpH hpq χ hprim hquad hchi d k hD)

theorem realCharacter_goodPrime_legendre_radicand
    {q : ℕ} [NeZero q] (H p : ℕ) [Fact p.Prime]
    (hH : 2 ≤ H) (hpH : H < p) (hpq : ¬ p ∣ 2 * q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hreal : IsRealCharacter χ)
    (hchi : χ (p : ZMod q) = -1)
    (d k : ℤ) (hD : signedConductor χ = k ^ 2 * d) :
    legendreSym p d = -1 := by
  exact goodPrime_legendre_radicand H p hH hpH hpq χ hprim
    (realCharacter_isQuadratic χ hreal) hchi d k hD

end Awei.W39


end SiegelZeros

end OAI
