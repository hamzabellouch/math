import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFourier

namespace OAI

/-! Normalization of the first local cubic Fourier factor. The inverse
different in the additive pairing contributes exactly the cubic character
of lambda; the remaining Gauss sum is the original normalized one. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaResidueFourier_lambda {p : Eisenstein} (hp : primaryPrime p) :
    (residueFourierChar p hp.2.ne_zero).mulShift (Ideal.Quotient.mk (modulus p) lambdaE)=
      residueAddChar p hp.2.ne_zero := by
  ext x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AddChar.mulShift_apply,← map_mul,residueFourierChar_mk,residueAddChar_mk,
    additivePhase_fourierChar]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  rw [lambdaE_coe]
  field_simp [traceLambda_ne_zero]

theorem cubicThetaPrimeFourier_one_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFourier p hp 1 1=
      cubicSymbol p lambdaE*(Real.sqrt (norm p):ℂ)*gauss p := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime (primary_coprime_lambda hp.1)
  have hg := gaussSum_mulShift (cubicResidueChar p hp) (residueFourierChar p hp.2.ne_zero) u
  have hc : cubicResidueChar p hp (u:Residues p)=cubicSymbol p lambdaE := by
    rw [hu,cubicResidueChar_mk,← cubicSymbol_prime hp]
  rw [hu,cubicThetaResidueFourier_lambda hp] at hg
  have hn : gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero)=
      (Real.sqrt (norm p):ℂ)*gauss p := by
    rw [gauss_prime hp,gaussAtPrime_eq_gaussSum hp]
    have hpN : (Real.sqrt (norm p):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hp.2.ne_zero)))
    rw [mul_inv_cancel_left₀ hpN]
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),map_one,AddChar.mulShift_one,pow_one]
  calc
    _ = cubicSymbol p lambdaE*gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero) := by
      rw [← hg]
      congr 1
      simpa only [hu] using hc
    _ = _ := by rw [hn]; ring

end CubicFirstMoment

end

end OAI
