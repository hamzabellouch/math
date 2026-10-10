import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeUnitBranch

namespace OAI

/-! The actual finite Fourier kernels of the cubed-prime branches.
Their additive support and exact multiplicity follow from finite inflation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubePrimeDivisor (p : Eisenstein) (k : Fin 3) : p∣p^(3-k.val) :=
  dvd_pow_self p (by have := k.isLt; omega)

def cubicThetaPrimeCubeFiniteGauss {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) : ℂ :=
  ∑' y : Residues (p^(3-k.val)),
    (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) y))^k.val*
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*y)

theorem cubicThetaPrimeCubeFiniteGauss_support {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) (hG : cubicThetaPrimeCubeFiniteGauss hp k h≠0) :
    p^(2-k.val)∣h := by
  let : Finite (Residues (p^(3-k.val))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^(3-k.val))) := Fintype.ofFinite _
  have he : p^(3-k.val)∣p*h := by
    apply residueFourier_inflation_support (pow_ne_zero _ hp.2.ne_zero)
      (cubicThetaPrimeCubePrimeDivisor p k) (fun y => (cubicResidueChar p hp y)^k.val) h
    simpa only [cubicThetaPrimeCubeFiniteGauss,tsum_fintype] using hG
  rw [show 3-k.val=(2-k.val)+1 by have := k.isLt; omega,pow_succ',
    mul_dvd_mul_iff_left hp.2.ne_zero] at he
  exact he

theorem cubicThetaPrimeCubeFiniteGauss_zero {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) (hh : ¬p^(2-k.val)∣h) :
    cubicThetaPrimeCubeFiniteGauss hp k h=0 := by
  by_contra he
  exact hh (cubicThetaPrimeCubeFiniteGauss_support hp k h he)

theorem cubicThetaPrimeCubeFiniteGauss_reduction {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) :
    cubicThetaPrimeCubeFiniteGauss hp k (p^(2-k.val)*h)=
      (norm (p^(2-k.val)):ℂ)*cubicThetaPrimeFourier p hp k.val h := by
  have he : p^(3-k.val)=p*p^(2-k.val) := by
    rw [←pow_succ']
    congr 1
    have := k.isLt
    omega
  exact residueFourier_inflation_of_eq (pow_ne_zero _ hp.2.ne_zero) hp.2.ne_zero
    (pow_ne_zero (2-k.val) hp.2.ne_zero) he (cubicThetaPrimeCubePrimeDivisor p k)
    (fun y : Residues p => (cubicResidueChar p hp y)^k.val) h

end CubicFirstMoment

end

end OAI
