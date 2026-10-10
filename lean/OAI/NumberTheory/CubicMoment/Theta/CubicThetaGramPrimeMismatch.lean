import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeKloostermanStationary
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanHermitian

namespace OAI

/-! Mismatched prime divisibility removes every higher prime-power
denominator from the actual off-diagonal Gram kernel. -/
noncomputable section
namespace CubicFirstMoment

private lemma inverse_square_representative {q d : Eisenstein} (hqd : IsCoprime q d) :
    ∃ j : Eisenstein,IsCoprime q j ∧ ∀ k : Eisenstein,
      Ideal.Quotient.mk (modulus q) k*(Ring.inverse (Ideal.Quotient.mk (modulus q) d))^2=
        Ideal.Quotient.mk (modulus q) (k*j) := by
  let r : Residues q := Ideal.Quotient.mk (modulus q) d
  let j := residueRepresentative q ((Ring.inverse r)^2)
  have hr : IsUnit r := residue_isUnit_of_isCoprime hqd
  refine ⟨j,?_,?_⟩
  · apply isCoprime_of_residue_isUnit
    change IsUnit (Ideal.Quotient.mk (modulus q) (residueRepresentative q ((Ring.inverse r)^2)))
    rw [residueRepresentative_spec]
    exact hr.ringInverse.pow 2
  · intro k
    rw [map_mul]
    dsimp only [j,r]
    rw [residueRepresentative_spec]

theorem cubicThetaKloostermanSum_prime_mismatch_zero {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hcp : IsCoprime c p)
    (n : ℕ) (h k : Eisenstein) (hh : p∣h) (hk : ¬p∣k) :
    cubicThetaKloostermanSum h k (p^(n+2)*c)
      (dvd_mul_of_dvd_right hc (p^(n+2)))=0 := by
  have hu : primary (p^(n+2)) := by
    rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
  have hcu : IsCoprime c (p^(n+2)) := hcp.pow_right
  have h3 := isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl (p^(n+2))))
  have huc : IsCoprime (p^(n+2)) (3*c) := h3.symm.mul_right hcu.symm
  obtain ⟨j,hj,htwist⟩ := inverse_square_representative huc
  have hjp : IsCoprime p j :=
    hj.of_isCoprime_of_dvd_left (dvd_pow_self p (by omega : n+2≠0))
  have hjn : ¬p∣j := hp.2.coprime_iff_not_dvd.mp hjp
  have hkj : ¬p∣k*j := by
    intro hd
    rcases hp.2.dvd_mul.mp hd with hd | hd
    · exact hk hd
    · exact hjn hd
  rw [cubicThetaKloostermanSum_factor hu hc hc0 hcu,htwist k,
    cubicThetaPrimeKloosterman_mismatch_zero hp n h (k*j) hh hkj,mul_zero,zero_mul]

theorem cubicThetaKloostermanSum_prime_mismatch_zero_symm {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hcp : IsCoprime c p)
    (n : ℕ) (h k : Eisenstein) (hh : ¬p∣h) (hk : p∣k) :
    cubicThetaKloostermanSum h k (p^(n+2)*c)
      (dvd_mul_of_dvd_right hc (p^(n+2)))=0 := by
  rw [cubicThetaKloostermanSum_hermitian (dvd_mul_of_dvd_right hc (p^(n+2)))
    (mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hc0)]
  rw [cubicThetaKloostermanSum_prime_mismatch_zero hp hc hc0 hcp n (-k) (-h)
    (dvd_neg.mpr hk) (fun hd => hh (dvd_neg.mp hd)),star_zero]

theorem cubicThetaKloostermanSum_primeFree_power_zero {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hcp : IsCoprime c p)
    (n : ℕ) (h k : Eisenstein) (hh : ¬p∣h) :
    cubicThetaKloostermanSum h (p*k) (p^(n+2)*c)
      (dvd_mul_of_dvd_right hc (p^(n+2)))=0 :=
  cubicThetaKloostermanSum_prime_mismatch_zero_symm hp hc hc0 hcp n h (p*k) hh (dvd_mul_right p k)

end CubicFirstMoment

end

end OAI
