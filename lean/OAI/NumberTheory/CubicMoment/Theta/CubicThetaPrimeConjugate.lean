import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeGauss

namespace OAI

/-! The second local cubic Fourier factor is the conjugate of the first.
The additive character uses the same inverse-different normalization. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFourier_two_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFourier p hp 2 1=star (cubicThetaPrimeFourier p hp 1 1) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let χ := cubicResidueChar p hp
  let ψ := residueFourierChar p hp.2.ne_zero
  have hi : χ^2=χ⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    exact cubicResidueChar_cube hp
  have hm : χ (-1:Residues p)=1 := by
    have he : (-1:Residues p)=Ideal.Quotient.mk (modulus p) (-1:Eisenstein) := by simp
    rw [he]
    change cubicResidueChar p hp (Ideal.Quotient.mk (modulus p) (-1:Eisenstein))=1
    rw [cubicResidueChar_mk,← cubicSymbol_prime hp,cubicSymbol_neg hp.1,cubicSymbol_prime hp]
    exact cubicSymbolAtPrime_one hp
  have hmi : χ⁻¹ (-1:Residues p)=1 := by
    rw [← MulChar.star_apply',hm,star_one]
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),cubicThetaPrimeFourier_gaussSum hp (by norm_num)]
  simp only [map_one,AddChar.mulShift_one,pow_one]
  change gaussSum (χ^2) ψ=star (gaussSum χ ψ)
  rw [star_gaussSum_eq,hi]
  have he := mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ
  rw [hmi,one_mul] at he
  exact he.symm

theorem cubicThetaPrimeFourier_two_unit {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeFourier p hp 2 h=
      cubicSymbol p h*star (cubicThetaPrimeFourier p hp 1 1) := by
  rw [cubicThetaPrimeFourier_unit hp (by norm_num) h hh,cubicThetaPrimeFourier_two_one hp,
    cubicSymbol_sq_eq_star hp.1,star_star]

end CubicFirstMoment

end

end OAI
