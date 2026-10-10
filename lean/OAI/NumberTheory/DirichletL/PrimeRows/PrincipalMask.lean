import OAI.NumberTheory.DirichletL.PrimeRows.Principal
import OAI.NumberTheory.DirichletL.PrimeRows.MarkedHolomorphic
import OAI.NumberTheory.DirichletL.Detector.CalibrationSupport

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_nonzero_supported (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (a : O)
    (ha : (calibrationForSet S hS).residueMonoid a≠0) : Supported (Ideal.span {a}) := by
  have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp ha
  have hc := (CubicEisenstein.isUnit_quotient_span_iff _ _).mp hu
  have havoid := (calibrationForSet_coprime_iff S hS a).mp hc
  rw [supported_span_iff]
  constructor
  · intro hd
    exact havoid (Ideal.span {λ₀}) (hbad (Finset.mem_insert_self _ _))
      (Ideal.mem_span_singleton.mpr hd)
  · intro hd
    exact havoid (Ideal.span {(2:O)}) (hbad (by simp [CanonicalQuadraticSieve.fixedBadPrimes]))
      (Ideal.mem_span_singleton.mpr hd)

theorem calibrated_row_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1)
    (hcal : (calibrationForSet S hmax).residueMonoid u.val≠0) :
    (rowCharacter S hS u).residue≠1 := fun hp=>hu
      (rowCharacter_principal_supported_eq_one S hS hbad u
        (calibration_nonzero_supported S hmax hbad u.val hcal) hp)

theorem principal_calibration_vanish (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1) (hp : (rowCharacter S hS u).residue=1) :
    (calibrationForSet S hmax).residueMonoid u.val=0 := by
  by_contra hn
  exact calibrated_row_nonprincipal S hS hmax hbad u hu hn hp

theorem calibrated_numerator_differentiable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1) :
    Differentiable ℂ (fun w=>star ((calibrationForSet S hmax).residueMonoid u.val)*
      HeckeOrigin.continued (rowCharacter S hS u) w) := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiable_const _
  · intro w
    exact (HeckeOrigin.continued_differentiableAt _
      (Or.inr (calibrated_row_nonprincipal S hS hmax hbad u hu hc))).const_mul _

theorem calibrated_physicalRow_first_differentiableAt_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z) w := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiableAt_const _
  · exact (physicalCompensatedRow_first_differentiableAt_w eps heps S hS hfirst T hT η u
      x w z hx hw hz hxw (Or.inr
        (calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc))).const_mul _

end SevenEighths.ProbeHighRowFamily

end

end OAI
