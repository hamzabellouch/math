import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeKloostermanInflation

namespace OAI

/-! The first-order unit shift in the actual prime-power residue ring.
The shift has square zero, so inversion has an exact linear formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRingInverse_add_square_zero {R : Type*} [CommRing R]
    (x e : R) (hx : IsUnit x) (he : e^2=0) :
    Ring.inverse (x+e)=Ring.inverse x-e*(Ring.inverse x)^2 := by
  have hm : (x+e)*(Ring.inverse x-e*(Ring.inverse x)^2)=1 := by
    calc
      _ = x*Ring.inverse x+e*Ring.inverse x*(1-x*Ring.inverse x)-e^2*(Ring.inverse x)^2 := by ring
      _ = 1 := by rw [Ring.mul_inverse_cancel x hx,he]; ring
  let u : Rˣ := ⟨x+e,Ring.inverse x-e*(Ring.inverse x)^2,hm,by simpa only [mul_comm] using hm⟩
  exact Ring.inverse_unit u

def cubicThetaPrimeKloostermanShift (p : Eisenstein) (n : ℕ) (b : Residues p) :
    Residues (p^(n+2)) :=
  Ideal.Quotient.mk (modulus (p^(n+2))) (p^(n+1)*residueRepresentative p b)

lemma cubicThetaPrimeKloostermanShift_square (p : Eisenstein) (n : ℕ) (b : Residues p) :
    (cubicThetaPrimeKloostermanShift p n b)^2=0 := by
  unfold cubicThetaPrimeKloostermanShift
  rw [←map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  rw [mul_pow,←pow_mul]
  exact dvd_mul_of_dvd_left (pow_dvd_pow p (by omega : n+2≤(n+1)*2)) _

lemma cubicThetaPrimeKloostermanShift_reduction (p : Eisenstein) (n : ℕ) (b : Residues p) :
    residueReduction (dvd_pow_self p (by omega : n+2≠0))
      (cubicThetaPrimeKloostermanShift p n b)=0 := by
  unfold cubicThetaPrimeKloostermanShift
  rw [residueReduction_mk]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero n)) _

lemma cubicThetaPrimeKloostermanWeight_shift {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (b : Residues p) (x : Residues (p^(n+2))) :
    cubicSymbol (p^(n+2)) (residueRepresentative (p^(n+2))
      (x+cubicThetaPrimeKloostermanShift p n b))=
      cubicSymbol (p^(n+2)) (residueRepresentative (p^(n+2)) x) := by
  rw [cubicThetaPrimePowerWeight_inflation hp (n+1),
    cubicThetaPrimePowerWeight_inflation hp (n+1),map_add,
    cubicThetaPrimeKloostermanShift_reduction,add_zero]

def cubicThetaPrimeKloostermanDerivative (p : Eisenstein) (n : ℕ) (h k : Eisenstein)
    (x : Residues (p^(n+2))) : Residues p :=
  Ideal.Quotient.mk (modulus p) h-Ideal.Quotient.mk (modulus p) k*
    (Ring.inverse (residueReduction (dvd_pow_self p (by omega : n+2≠0)) x))^2

lemma cubicThetaPrimeKloostermanPhase_shift {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein) (b : Residues p) (x : Residues (p^(n+2))) (hx : IsUnit x) :
    residueFourierChar (p^(n+2)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+2))) h*(x+cubicThetaPrimeKloostermanShift p n b)+
        Ideal.Quotient.mk (modulus (p^(n+2))) k*
          Ring.inverse (x+cubicThetaPrimeKloostermanShift p n b))=
      residueFourierChar (p^(n+2)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(n+2))) h*x+
          Ideal.Quotient.mk (modulus (p^(n+2))) k*Ring.inverse x)*
        residueFourierChar p hp.2.ne_zero (b*cubicThetaPrimeKloostermanDerivative p n h k x) := by
  let d : Residues (p^(n+2)) := Ideal.Quotient.mk (modulus (p^(n+2))) h-
    Ideal.Quotient.mk (modulus (p^(n+2))) k*(Ring.inverse x)^2
  have hd : residueReduction (dvd_pow_self p (by omega : n+2≠0)) d=
      cubicThetaPrimeKloostermanDerivative p n h k x := by
    dsimp only [d,cubicThetaPrimeKloostermanDerivative]
    rw [map_sub,map_mul,map_pow,residueReduction_mk,residueReduction_mk,
      cubicThetaPrimePowerReduction_inverse hp (n+1)]
  have he : residueFourierChar (p^(n+2)) (pow_ne_zero _ hp.2.ne_zero)
      (cubicThetaPrimeKloostermanShift p n b*d)=
      residueFourierChar p hp.2.ne_zero (b*cubicThetaPrimeKloostermanDerivative p n h k x) := by
    have ht := cubicThetaResidueFourier_factor (pow_ne_zero (n+2) hp.2.ne_zero)
      hp.2.ne_zero (pow_ne_zero (n+1) hp.2.ne_zero) (pow_succ' p (n+1))
      (dvd_pow_self p (by omega : n+2≠0)) (residueRepresentative p b) d
    rw [residueRepresentative_spec,hd] at ht
    exact ht
  have hi := cubicThetaRingInverse_add_square_zero x (cubicThetaPrimeKloostermanShift p n b)
    hx (cubicThetaPrimeKloostermanShift_square p n b)
  have ha : Ideal.Quotient.mk (modulus (p^(n+2))) h*(x+cubicThetaPrimeKloostermanShift p n b)+
      Ideal.Quotient.mk (modulus (p^(n+2))) k*
        Ring.inverse (x+cubicThetaPrimeKloostermanShift p n b)=
      (Ideal.Quotient.mk (modulus (p^(n+2))) h*x+
        Ideal.Quotient.mk (modulus (p^(n+2))) k*Ring.inverse x)+
        cubicThetaPrimeKloostermanShift p n b*d := by
    rw [hi]
    dsimp only [d]
    ring
  rw [ha,AddChar.map_add_eq_mul,he]

end CubicFirstMoment

end

end OAI
