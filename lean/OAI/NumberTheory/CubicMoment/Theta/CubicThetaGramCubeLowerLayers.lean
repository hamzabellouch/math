import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanZeroIndices
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanUnitScale

namespace OAI

/-! The lower denominator layers of the actual Gram kernel at two
cubically multiplied frequencies. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeIndex_zero (p h : Eisenstein) (j : ℕ) (hj : j ≤ 3) :
    Ideal.Quotient.mk (modulus (p^j)) (p^3*h)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
    (dvd_mul_of_dvd_left (pow_dvd_pow p hj) h))

theorem cubicThetaKloostermanSum_cube_layer_one {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0) (hdp : IsCoprime d p)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum (p^3*h) (p^3*k) (p*d)
      (dvd_mul_of_dvd_right hd p)=0 := by
  rw [cubicThetaKloostermanSum_factor hp.1 hd hd0 hdp]
  have hz (a : Eisenstein) : Ideal.Quotient.mk (modulus p) (p^3*a)=0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (dvd_mul_of_dvd_left (dvd_pow_self p (by decide : 3≠0)) a))
  rw [hz,hz,zero_mul,cubicThetaSymbolKloosterman_prime_origin hp,mul_zero,zero_mul]

theorem cubicThetaKloostermanSum_cube_layer_two {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0) (hdp : IsCoprime d p)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum (p^3*h) (p^3*k) (p^2*d)
      (dvd_mul_of_dvd_right hd (p^2))=0 := by
  have hu : primary (p^2) := by
    rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
  rw [cubicThetaKloostermanSum_factor hu hd hd0 hdp.pow_right,
    cubicThetaPrimeCubeIndex_zero p h 2 (by decide),
    cubicThetaPrimeCubeIndex_zero p k 2 (by decide),zero_mul,
    cubicThetaSymbolKloosterman_square_zero hp,mul_zero,zero_mul]

lemma cubicThetaFiniteKloosterman_cube_unit {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0) (hdp : IsCoprime d p)
    (h k : Residues (3*d)) :
    cubicThetaFiniteKloosterman d hd0
      (h*Ideal.Quotient.mk (modulus (3*d)) (p^3))
      (k*Ring.inverse (Ideal.Quotient.mk (modulus (3*d)) (p^3)))=
        cubicThetaFiniteKloosterman d hd0 h k := by
  have hu : primary (p^3) := by
    rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
  have he := cubicThetaFiniteKloosterman_unit_scale hd hd0 hu hdp.pow_right h k
  rw [cubicThetaSymbol_prime_pow hp,cubicSymbol_cube_of_isCoprime hp.1 d hdp.symm,
    one_mul] at he
  exact he.symm

theorem cubicThetaKloostermanSum_cube_layer_three {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0) (hdp : IsCoprime d p)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum (p^3*h) (p^3*k) (p^3*d)
      (dvd_mul_of_dvd_right hd (p^3))=
      (norm (p^2):ℂ)*((norm p:ℂ)-1)*cubicThetaKloostermanSum h k d hd := by
  have hu : primary (p^3) := by
    rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
  have hp3 : IsCoprime p (3:Eisenstein) :=
    (isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))).symm
  have hs (a : Eisenstein) (ha : IsCoprime p a) : cubicSymbol (p^3) a=1 := by
    rw [cubicThetaSymbol_prime_pow hp,cubicSymbol_cube_of_isCoprime hp.1 a ha]
  have hU : IsUnit (Ideal.Quotient.mk (modulus (3*d)) (p^3)) :=
    residue_isUnit_of_isCoprime (hp3.mul_right hdp.symm).pow_left.symm
  have hi : Ideal.Quotient.mk (modulus (3*d)) (p^3*k)*
      (Ring.inverse (Ideal.Quotient.mk (modulus (3*d)) (p^3)))^2=
      Ideal.Quotient.mk (modulus (3*d)) k*
        Ring.inverse (Ideal.Quotient.mk (modulus (3*d)) (p^3)) := by
    rw [map_mul]
    calc
      _ = Ideal.Quotient.mk (modulus (3*d)) k*
          (Ideal.Quotient.mk (modulus (3*d)) (p^3)*
            Ring.inverse (Ideal.Quotient.mk (modulus (3*d)) (p^3)))*
              Ring.inverse (Ideal.Quotient.mk (modulus (3*d)) (p^3)) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ hU,mul_one]
  rw [cubicThetaKloostermanSum_factor hu hd hd0 hdp.pow_right,
    hs (3*d) (hp3.mul_right hdp.symm),hs d hdp.symm,one_mul,
    cubicThetaPrimeCubeIndex_zero p h 3 (by decide),
    cubicThetaPrimeCubeIndex_zero p k 3 (by decide),zero_mul,
    cubicThetaSymbolKloosterman_cube_zero hp,one_mul,hi,map_mul,
    mul_comm (Ideal.Quotient.mk (modulus (3*d)) (p^3)),
    cubicThetaFiniteKloosterman_cube_unit hp hd hd0 hdp,
    cubicThetaFiniteKloosterman_integer h k hd hd0]

end CubicFirstMoment

end

end OAI
