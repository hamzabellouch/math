import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeConjugate

namespace OAI

/-! Exact local factors at the first four powers, including zero
frequencies and the cubic return to the first character. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFourier_one_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaPrimeFourier p hp 1 (p*h)=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),pow_one]
  have hz : Ideal.Quotient.mk (modulus p) (p*h)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right p h))
  rw [hz,AddChar.mulShift_zero]
  exact gaussSum_one_right (cubicResidueChar_ne_one hp)

lemma cubicThetaPrimeFourier_two_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaPrimeFourier p hp 2 (p*h)=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num)]
  have hz : Ideal.Quotient.mk (modulus p) (p*h)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right p h))
  rw [hz,AddChar.mulShift_zero]
  apply gaussSum_one_right
  intro he
  have hc := cubicResidueChar_cube hp
  rw [show (3:ℕ)=2+1 by omega,pow_succ,he,one_mul] at hc
  exact cubicResidueChar_ne_one hp hc

lemma cubicThetaLocalPrimePowerGauss_prime_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 1 (p*h)=0 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 0 (p*h)
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 1 (p^0*(p*h))=
    (norm (p^0):ℂ)*cubicThetaPrimeFourier p hp 1 (p*h) at he
  rw [cubicThetaPrimeFourier_one_multiple hp,mul_zero] at he
  simpa only [pow_zero,one_mul] using he

lemma cubicThetaLocalPrimePowerGauss_square_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^2*h)=0 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 1 (p*h)
  have hx : p^1*(p*h)=p^2*h := by ring
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^1*(p*h))=
    (norm (p^1):ℂ)*cubicThetaPrimeFourier p hp 2 (p*h) at he
  rw [hx,cubicThetaPrimeFourier_two_multiple hp,mul_zero] at he
  exact he

lemma cubicThetaLocalPrimePowerGauss_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=
      (norm (p^2):ℂ)*(if p ∣ h then (norm p:ℂ)-1 else -1) := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 2 h
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=
    (norm (p^2):ℂ)*cubicThetaPrimeFourier p hp 3 h at he
  rw [he,cubicThetaPrimeFourier_three hp]

lemma cubicThetaLocalPrimePowerGauss_fourth {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 4 (p^3*h)=
      (norm (p^3):ℂ)*cubicThetaPrimeFourier p hp 1 h := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 3 h
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 4 (p^3*h)=
    (norm (p^3):ℂ)*cubicThetaPrimeFourier p hp (1+3) h at he
  rw [he,cubicThetaPrimeFourier_period hp (by norm_num)]

end CubicFirstMoment

end

end OAI
