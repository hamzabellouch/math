import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanCRT
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePowerFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitLifting

namespace OAI

/-! Exact prime-power conductor reduction for the local Kloosterman
factor. It retains the inverse term and applies to its zero extension. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimePowerReduction_isUnit {p : Eisenstein} (_hp : primaryPrime p)
    (n : ℕ) (x : Residues (p^(n+1))) :
    IsUnit x ↔ IsUnit (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x) := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [residueReduction_mk,cubicTheta_residue_mk_isUnit_iff,cubicTheta_residue_mk_isUnit_iff]
  exact IsCoprime.pow_left_iff (Nat.succ_pos n)

lemma cubicThetaPrimePowerReduction_inverse {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (x : Residues (p^(n+1))) :
    residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) (Ring.inverse x)=
      Ring.inverse (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x) := by
  by_cases hx : IsUnit x
  · exact cubicThetaResidueHom_inverse _ hx
  · have hy : ¬IsUnit (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x) :=
      fun hy => hx ((cubicThetaPrimePowerReduction_isUnit hp n x).mpr hy)
    rw [Ring.inverse_non_unit _ hx,Ring.inverse_non_unit _ hy,map_zero]

lemma cubicThetaResidueFourier_factor {q d k : Eisenstein} (hq : q≠0)
    (hd : d≠0) (hk : k≠0) (hf : q=d*k) (hdq : d∣q)
    (h : Eisenstein) (x : Residues q) :
    residueFourierChar q hq (Ideal.Quotient.mk (modulus q) (k*h)*x)=
      residueFourierChar d hd (Ideal.Quotient.mk (modulus d) h*residueReduction hdq x) := by
  subst q
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [←map_mul,residueReduction_mk,←map_mul]
  simpa only [mul_assoc] using residueFourierChar_mul_factor hd hk h a

def cubicThetaPrimeKloosterman (p : Eisenstein) (hp : primaryPrime p)
    (j : ℕ) (h k : Eisenstein) : ℂ :=
  ∑' x : Residues p,(cubicResidueChar p hp x)^j*
    residueFourierChar p hp.2.ne_zero
      (Ideal.Quotient.mk (modulus p) h*x+Ideal.Quotient.mk (modulus p) k*Ring.inverse x)

lemma cubicThetaPrimeKloosterman_amplitude {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (k : Eisenstein) (x : Residues (p^(n+1))) :
    cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1)) x)*
      residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*k)*Ring.inverse x)=
      (cubicResidueChar p hp (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x))^(n+1)*
        residueFourierChar p hp.2.ne_zero
          (Ideal.Quotient.mk (modulus p) k*
            Ring.inverse (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x)) := by
  rw [cubicThetaPrimePowerWeight_inflation hp,
    cubicThetaResidueFourier_factor (pow_ne_zero _ hp.2.ne_zero) hp.2.ne_zero
      (pow_ne_zero n hp.2.ne_zero) (pow_succ' p n)
      (dvd_pow_self p (Nat.succ_ne_zero n)),cubicThetaPrimePowerReduction_inverse hp]

theorem cubicThetaPrimeKloosterman_support {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein)
    (hK : cubicThetaSymbolKloosterman (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+1))) h)
      (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*k))≠0) : p^n∣h := by
  let : Finite (Residues (p^(n+1))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^(n+1))) := Fintype.ofFinite _
  have he : p^(n+1)∣p*h := by
    apply residueFourier_inflation_support (pow_ne_zero _ hp.2.ne_zero)
      (dvd_pow_self p (Nat.succ_ne_zero n))
      (fun y : Residues p => (cubicResidueChar p hp y)^(n+1)*
        residueFourierChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) k*Ring.inverse y)) h
    contrapose! hK
    unfold cubicThetaSymbolKloosterman
    simp only [tsum_fintype,AddChar.map_add_eq_mul]
    convert hK using 1
    apply Finset.sum_congr rfl
    intro x _
    rw [show cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1)) x)*
      (residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
          (Ideal.Quotient.mk (modulus (p^(n+1))) h*x)*
        residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
          (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*k)*Ring.inverse x))=
      (cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1)) x)*
        residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
          (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*k)*Ring.inverse x))*
        residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
          (Ideal.Quotient.mk (modulus (p^(n+1))) h*x) by ring,
      cubicThetaPrimeKloosterman_amplitude hp]
  rwa [pow_succ,mul_comm (p^n) p,mul_dvd_mul_iff_left hp.2.ne_zero] at he

theorem cubicThetaPrimeKloosterman_reduction {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein) :
    cubicThetaSymbolKloosterman (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*h))
      (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*k))=
      (norm (p^n):ℂ)*cubicThetaPrimeKloosterman p hp (n+1) h k := by
  let f : Residues p → ℂ := fun y => (cubicResidueChar p hp y)^(n+1)*
    residueFourierChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) k*Ring.inverse y)
  have he := residueFourier_inflation_of_eq (pow_ne_zero _ hp.2.ne_zero) hp.2.ne_zero
    (pow_ne_zero n hp.2.ne_zero) (pow_succ' p n)
    (dvd_pow_self p (Nat.succ_ne_zero n)) f h
  calc
    _ = ∑' x : Residues (p^(n+1)),f (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x)*
        residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
          (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*h)*x) := by
      apply tsum_congr
      intro x
      rw [AddChar.map_add_eq_mul]
      calc
        _ = (cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1)) x)*
          residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
            (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*k)*Ring.inverse x))*
          residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
            (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*h)*x) := by ring
        _ = _ := by rw [cubicThetaPrimeKloosterman_amplitude hp]
    _ = (norm (p^n):ℂ)*∑' y : Residues p,f y*
        residueFourierChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h*y) := he
    _ = _ := by
      congr 1
      apply tsum_congr
      intro y
      dsimp only [f,cubicThetaPrimeKloosterman]
      rw [AddChar.map_add_eq_mul]
      ring

end CubicFirstMoment

end

end OAI
