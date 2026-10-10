import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteInflation

namespace OAI

/-! The local conductor restriction for cubic Gauss coefficients at an
unramified prime power. The weight is the literal cubic residue symbol. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaSymbol_prime_pow {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (x : Eisenstein) : cubicSymbol (p^n) x=(cubicSymbol p x)^n := by
  induction n with
  | zero => rw [pow_zero,pow_zero,cubicSymbol_one_lower]
  | succ n ih =>
    rw [pow_succ,cubicSymbol_mul_lower (pow_ne_zero n hp.2.ne_zero) hp.2.ne_zero,ih,pow_succ]

def cubicThetaLocalPrimePowerGauss (p : Eisenstein) (hp : p≠0) (n : ℕ)
    (h : Eisenstein) : ℂ :=
  ∑' x : Residues (p^n), cubicSymbol (p^n) (residueRepresentative (p^n) x)*
    residueFourierChar (p^n) (pow_ne_zero n hp) (Ideal.Quotient.mk (modulus (p^n)) h*x)

lemma cubicThetaPrimePowerWeight_inflation {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (x : Residues (p^(n+1))) :
    cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1)) x)=
      (cubicResidueChar p hp
        (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x))^(n+1) := by
  rw [cubicThetaSymbol_prime_pow hp]
  congr 1
  have he : residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x=
      Ideal.Quotient.mk (modulus p) (residueRepresentative (p^(n+1)) x) := by
    exact (congrArg (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)))
      (residueRepresentative_spec (p^(n+1)) x)).symm
  rw [he,cubicResidueChar_mk,cubicSymbol_prime hp]

theorem cubicThetaLocalPrimePowerGauss_support {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein)
    (hG : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+1) h≠0) : p^n ∣ h := by
  let : Finite (Residues (p^(n+1))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^(n+1))) := Fintype.ofFinite _
  have he : p^(n+1) ∣ p*h := by
    apply residueFourier_inflation_support (pow_ne_zero _ hp.2.ne_zero)
      (dvd_pow_self p (Nat.succ_ne_zero n)) (fun x => (cubicResidueChar p hp x)^(n+1)) h
    simpa only [cubicThetaLocalPrimePowerGauss,tsum_fintype,
      cubicThetaPrimePowerWeight_inflation hp] using hG
  rwa [pow_succ,mul_comm (p^n) p,mul_dvd_mul_iff_left hp.2.ne_zero] at he

theorem cubicThetaLocalPrimePowerGauss_eq_zero {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) (hh : ¬p^n ∣ h) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+1) h=0 := by
  by_contra hn
  exact hh (cubicThetaLocalPrimePowerGauss_support hp n h hn)

theorem cubicThetaLocalPrimePowerGauss_reduction {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+1) (p^n*h)=
      (norm (p^n):ℂ)*∑' y : Residues p, (cubicResidueChar p hp y)^(n+1)*
        residueFourierChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h*y) := by
  unfold cubicThetaLocalPrimePowerGauss
  simp_rw [cubicThetaPrimePowerWeight_inflation hp]
  exact residueFourier_inflation_of_eq (pow_ne_zero _ hp.2.ne_zero) hp.2.ne_zero
    (pow_ne_zero n hp.2.ne_zero) (pow_succ' p n)
    (dvd_pow_self p (Nat.succ_ne_zero n))
    (fun y : Residues p => (cubicResidueChar p hp y)^(n+1)) h

end CubicFirstMoment

end

end OAI
