import OAI.NumberTheory.DirichletL.Detector.FixedEuler
import OAI.NumberTheory.DirichletL.Detector.GlobalCorrection

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem principalHigh_L_factorization (S : Finset Id) (hS : ∀P∈S,Prime P)
    (hgood : ∀P : PrimeIdeal,P.val∉S → Supported P.val) (htail : CorrectionTail S)
    (η : Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hH := globalClosedCorrection_multipliable η S htail x w z (by linarith) (by linarith) (by linarith)
  have he := (((fixedSourcePrincipal_hasProd S hS (6*z) hz1).mul
    (fixedSourcePrincipal_hasProd S hS w hw1)).mul
      ((excludedTarget_hasProd η S hS x hx1).inv₀
        (LFunction_ne_zero_of_one_lt_re (η.excludePrimes S hS) hx1))).mul hH.hasProd
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ((1-CubicEisenstein.fullIdealWeight (6*z) P.val.val)⁻¹ *
       (1-CubicEisenstein.fullIdealWeight w P.val.val)⁻¹ *
       ((1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight x P.val.val)⁻¹)⁻¹) *
       idealClosedCorrection η P.val x w z = idealHighLocalFactor η P.val.val x w z := by
    rw [idealHighLocalFactor_rational η P.val (hgood P.val P.property) x w z hx hw hz]
    simp only [CubicEisenstein.fullIdealWeight,P.val.property.ne_zero,ite_false,
      Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev,inv_inv]
    rw [show -(6*z)=(-6:ℂ)*z by ring]
    ring
  have he' : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z) := by
    simpa only [hlocal,div_eq_mul_inv,globalClosedCorrection] using he
  exact (excludedIdealHighSeries_hasProd_outside S hS η x w z hx hw hz).unique he'

end SevenEighths.ProbePhysical
end

end OAI
