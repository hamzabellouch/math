import OAI.NumberTheory.DirichletL.PrimeRows.Moments
import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

theorem momentData_product_raw (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData χ).character (momentElement u)) I=
      idealCoeff (χ.product (rawRow u)) I := by
  have he : idealCoeff ((momentData χ).character (momentElement u))=
      idealCoeff (χ.product (rawRow u)) := by
    apply hom_eq_of_primes
    intro P
    rw [momentData_coeff,idealCoeff_product,rawRow_coeff,fixedSourcePrincipal_prime]
    simp
  exact congrArg (fun f : Ideal O→*₀ℂ=>f I) he

theorem inverse_row_twist_moment_coeff (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((rawRow u).inverse.product χ) I=
      conj (idealCoeff ((momentData χ.inverse).character (momentElement u)) I) := by
  rw [momentData_product_raw,idealCoeff_product,idealCoeff_product,
    idealCoeff_inverse_conj,idealCoeff_inverse_conj,map_mul]
  simp only [starRingEnd_self_apply]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→RowData :=
  Sum.elim (fun b=>if b then momentData (fixedSourcePrincipal S hS)
    else momentData (η.inverse.excludePrimes S hS))
    (fun θ=>momentData (HeckeRayQuotient.character M H hH θ).inverse)

def sourceMomentReverse : Sum Bool (RayQuotient.Characters M H)→Bool :=
  Sum.elim (fun b=>!b) (fun _=>true)

theorem source_family_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    idealCoeff (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) I=
      if sourceMomentReverse M H j then
        conj (idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I)
      else idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I := by
  rcases j with b|θ
  · cases b
    · simpa [sourceMomentReverse,sourceMomentData] using denominator_moment_coeff S hS hbad η u I
    · simpa [sourceMomentReverse,sourceMomentData] using numerator_moment_coeff S hS hbad u I
  · exact inverse_row_twist_moment_coeff (HeckeRayQuotient.character M H hH θ) u I
end SevenEighths.ProbeHighRowFamily

end

end OAI
