import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeConjugate

namespace OAI

/-! Finite cubic Gauss factors with the additive character of the original
arithmetic normalization. These are the off-diagonal finite factors needed
in the unramified critical intertwining calculation. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeAdditiveGauss (p : Eisenstein) (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) : ℂ :=
  ∑' y : Residues p, (cubicResidueChar p hp y)^n*
    residueAddChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h*y)

lemma cubicThetaPrimeAdditiveGauss_fourier {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) :
    cubicThetaPrimeAdditiveGauss p hp n h=cubicThetaPrimeFourier p hp n (lambdaE*h) := by
  unfold cubicThetaPrimeAdditiveGauss cubicThetaPrimeFourier
  apply tsum_congr
  intro y
  rw [←cubicThetaResidueFourier_lambda hp,AddChar.mulShift_apply,
    map_mul (Ideal.Quotient.mk (modulus p)) lambdaE h]
  congr 2
  ring

lemma cubicThetaPrimeAdditiveGauss_one {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 1 h=
      star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hh
  have he : Ideal.Quotient.mk (modulus p) h=(u:Residues p) := hu.symm
  have hg : cubicThetaPrimeAdditiveGauss p hp 1 h=
      gaussSum (cubicResidueChar p hp)
        ((residueAddChar p hp.2.ne_zero).mulShift (Ideal.Quotient.mk (modulus p) h)) := by
    simp only [cubicThetaPrimeAdditiveGauss,tsum_fintype,gaussSum,pow_one,AddChar.mulShift_apply]
  rw [hg,he,gaussSum_mulShift_eq,←MulChar.star_apply',hu,cubicResidueChar_mk,←cubicSymbol_prime hp]
  have hn : gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero)=
      (Real.sqrt (norm p):ℂ)*gauss p := by
    rw [gauss_prime hp,gaussAtPrime_eq_gaussSum hp]
    have hq : (Real.sqrt (norm p):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hp.2.ne_zero)))
    rw [mul_inv_cancel_left₀ hq]
  rw [hn]
  ring

lemma cubicThetaPrimeAdditiveGauss_two {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 2 h=star (cubicThetaPrimeAdditiveGauss p hp 1 h) := by
  have hcop : IsCoprime p (lambdaE*h) := (primary_coprime_lambda hp.1).mul_right hh
  rw [cubicThetaPrimeAdditiveGauss_fourier,cubicThetaPrimeAdditiveGauss_fourier,
    cubicThetaPrimeFourier_two_unit hp _ hcop,cubicThetaPrimeFourier_unit hp (by norm_num) _ hcop,
    pow_one,star_mul,star_star]
  ring

lemma cubicThetaPrimeAdditiveGauss_norm {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    ‖cubicThetaPrimeAdditiveGauss p hp 1 h‖=Real.sqrt (norm p) := by
  rw [cubicThetaPrimeAdditiveGauss_one hp h hh,norm_mul,norm_mul,norm_star,
    norm_cubicSymbol_of_isCoprime hp.1 hh,gauss_prime hp,norm_gaussAtPrime hp,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),one_mul,mul_one]

lemma cubicThetaPrimeAdditiveGauss_product {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 1 h*cubicThetaPrimeAdditiveGauss p hp 2 h=(norm p:ℂ) := by
  rw [cubicThetaPrimeAdditiveGauss_two hp h hh]
  have hn := cubicThetaPrimeAdditiveGauss_norm hp h hh
  have hq := Real.sq_sqrt (norm_nonneg p)
  rw [Complex.star_def,Complex.mul_conj',hn,←Complex.ofReal_pow,hq]

end CubicFirstMoment

end

end OAI
