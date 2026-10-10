import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorCharacter
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeCharacter

namespace OAI

/-! The angular numerator character on the original modulus `9*v`.
The finite correction at three is absorbed into this modulus, so its norm
bound remains `81*N(v)`. -/
noncomputable section
namespace CubicFirstMoment

def angularNumeratorLift (v : Eisenstein) (ℓ : ℤ) (x : Eisenstein) : ℂ :=
  cubicNumeratorLift v x*angularUnitCorrection ℓ x

lemma angularNumeratorLift_congr (hpub : CubicSupplementaryPeriodicity)
    {v x y : Eisenstein} (hv : v ≠ 0) (ℓ : ℤ)
    (h : Ideal.Quotient.mk (modulus (9*v)) x=Ideal.Quotient.mk (modulus (9*v)) y) :
    angularNumeratorLift v ℓ x=angularNumeratorLift v ℓ y := by
  have hd : 9*v ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have h3 : (3:Eisenstein) ∣ x-y := (show (3:Eisenstein) ∣ 9*v from ⟨3*v,by ring⟩).trans hd
  rw [angularNumeratorLift,angularNumeratorLift,cubicNumeratorLift_congr hpub hv h,
    angularUnitCorrection_congr ℓ (residue_eq_of_dvd_sub h3)]

lemma angularNumeratorLift_mul (v x y : Eisenstein) (ℓ : ℤ) :
    angularNumeratorLift v ℓ (x*y)=angularNumeratorLift v ℓ x*angularNumeratorLift v ℓ y := by
  simp only [angularNumeratorLift,cubicNumeratorLift_mul,angularUnitCorrection_mul]
  ring

def angularNumeratorChar (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) : MulChar (Residues (9*v)) ℂ where
  toFun x := angularNumeratorLift v ℓ (residueRepresentative (9*v) x)
  map_one' := by
    rw [angularNumeratorLift_congr hpub hv ℓ (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) 1)=
        Ideal.Quotient.mk (modulus (9*v)) 1 by rw [residueRepresentative_spec,map_one])]
    simp only [angularNumeratorLift,cubicNumeratorLift_one,angularUnitCorrection_one,one_mul]
  map_mul' x y := by
    rw [angularNumeratorLift_congr hpub hv ℓ (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) (x*y))=
        Ideal.Quotient.mk (modulus (9*v))
          (residueRepresentative (9*v) x*residueRepresentative (9*v) y) by
            rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact angularNumeratorLift_mul v _ _ ℓ
  map_nonunit' x hx := by
    have hn : ¬IsUnit (Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) x)) :=
      by rwa [residueRepresentative_spec]
    simp only [angularNumeratorLift,cubicNumeratorLift_nonunit hn,zero_mul]

lemma angularNumeratorChar_mk (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) (x : Eisenstein) :
    angularNumeratorChar hpub v hv ℓ (Ideal.Quotient.mk (modulus (9*v)) x)=
      angularNumeratorLift v ℓ x :=
  angularNumeratorLift_congr hpub hv ℓ (residueRepresentative_spec _ _)

lemma angularNumeratorChar_primary (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) {x : Eisenstein} (hx : primary x) :
    angularNumeratorChar hpub v hv ℓ (Ideal.Quotient.mk (modulus (9*v)) x)=cubicSymbol x v := by
  rw [angularNumeratorChar_mk,angularNumeratorLift,cubicNumeratorLift_primary v hx,
    angularUnitCorrection_primary hx,mul_one]

lemma angularNumeratorChar_compatible (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) :
    AngularUnitCompatible (9*v) (angularNumeratorChar hpub v hv ℓ) ℓ := by
  intro u
  rw [angularNumeratorChar_mk,angularNumeratorLift,cubicNumeratorLift_unit v u.isUnit,one_mul]
  simpa only [angularCorrectionChar_mk] using angularCorrectionChar_unit ℓ u

end CubicFirstMoment

end

end OAI
