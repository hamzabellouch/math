import OAI.NumberTheory.DirichletL.PrimeRows.MarkedCoordinates
import OAI.NumberTheory.DirichletL.PrimeRows.Agreement
import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedActual
import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedRamified

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedCompensatedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z B q : ℂ) : ℂ :=
  ProbeLocal.compensatedReplacement (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z) B q

theorem localNormalization_coordinates (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) :
    localNormalization η u P x w z=
      (1-coordV P.val.absNorm z)*(1-coordW P.val.absNorm (idealRowHom u.val P.val) w)/
        (1-coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x) := by
  unfold localNormalization coordV coordW coordD CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false,Complex.ofReal_natCast]
  rw [show -(6*z)=(-6:ℂ)*z by ring]
  rfl

theorem row_phase_ramified (u : FreeRow) (P : PrimeIdeal) (hP : P.val∣Ideal.span {u.val}) :
    idealRowHom u.val P.val=0 := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  exact idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu

theorem continuedCompensatedLocal_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      ramifiedSelected p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        x w z (multiplicity p u.val) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have he := ramifiedSelected_eq_replacement p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)
  rw [he]
  unfold continuedCompensatedLocal
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,zero_mul,mul_zero,star_zero]
  rw [←targetMonoid_primaryGenerator η P.val hs]
  unfold continuedMarkedLocal
  simp only [hspan]
  rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI
