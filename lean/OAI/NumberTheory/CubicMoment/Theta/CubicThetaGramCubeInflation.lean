import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeLowerLayers
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanCubeInflation

namespace OAI

/-! Exact removal of a common cubic factor from the full arithmetic
Kloosterman row, including its coprime denominator and both CRT phases. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFiniteKloosterman_cube_rescale {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0) (hdp : IsCoprime d p)
    (n : ℕ) (h k : Eisenstein) :
    cubicThetaFiniteKloosterman d hd0
      (Ideal.Quotient.mk (modulus (3*d)) (p^3*h))
      (Ideal.Quotient.mk (modulus (3*d)) (p^3*k)*
        (Ring.inverse (Ideal.Quotient.mk (modulus (3*d)) (p^(n+4))))^2)=
    cubicThetaFiniteKloosterman d hd0 (Ideal.Quotient.mk (modulus (3*d)) h)
      (Ideal.Quotient.mk (modulus (3*d)) k*
        (Ring.inverse (Ideal.Quotient.mk (modulus (3*d)) (p^(n+1))))^2) := by
  have hp3 : IsCoprime p (3:Eisenstein) :=
    (isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))).symm
  have hU : IsUnit (Ideal.Quotient.mk (modulus (3*d)) (p^3)) :=
    residue_isUnit_of_isCoprime (hp3.mul_right hdp.symm).pow_left.symm
  have hf : p^(n+4)=p^(n+1)*p^3 := by rw [←pow_add]
  let U := Ideal.Quotient.mk (modulus (3*d)) (p^3)
  let T := Ideal.Quotient.mk (modulus (3*d)) (p^(n+1))
  let H := Ideal.Quotient.mk (modulus (3*d)) h
  let K := Ideal.Quotient.mk (modulus (3*d)) k
  rw [map_mul,map_mul,hf,map_mul,Ring.inverse_mul (Or.inr hU)]
  change cubicThetaFiniteKloosterman d hd0 (U*H) ((U*K)*(Ring.inverse U*Ring.inverse T)^2)=_
  have hi : (U*K)*(Ring.inverse U*Ring.inverse T)^2=
      (K*(Ring.inverse T)^2)*Ring.inverse U := by
    calc
      _ = (K*(Ring.inverse T)^2)*(U*Ring.inverse U)*Ring.inverse U := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ hU,mul_one]
  rw [hi,mul_comm U H]
  exact cubicThetaFiniteKloosterman_cube_unit hp hd hd0 hdp H (K*(Ring.inverse T)^2)

theorem cubicThetaKloostermanSum_cubeInflation {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0) (hdp : IsCoprime d p)
    (n : ℕ) (h k : Eisenstein) :
    cubicThetaKloostermanSum (p^3*h) (p^3*k) (p^(n+4)*d)
      (dvd_mul_of_dvd_right hd (p^(n+4)))=
      (norm (p^3):ℂ)*cubicThetaKloostermanSum h k (p^(n+1)*d)
        (dvd_mul_of_dvd_right hd (p^(n+1))) := by
  have hu (j : ℕ) : primary (p^j) := by
    rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
  have hp3 : IsCoprime p (3:Eisenstein) :=
    (isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))).symm
  have h3d : IsCoprime p (3*d) := hp3.mul_right hdp.symm
  have hs (a : Eisenstein) (ha : IsCoprime p a) :
      cubicSymbol (p^(n+4)) a=cubicSymbol (p^(n+1)) a := by
    rw [cubicThetaSymbol_prime_pow hp,cubicThetaSymbol_prime_pow hp,
      show n+4=(n+1)+3 by omega,pow_add,cubicSymbol_cube_of_isCoprime hp.1 a ha,mul_one]
  have hi : IsUnit (Ideal.Quotient.mk (modulus (p^(n+4))) (3*d)) :=
    residue_isUnit_of_isCoprime h3d.pow_left
  have hl : cubicThetaSymbolKloosterman (p^(n+4)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+4))) (p^3*h))
      (Ideal.Quotient.mk (modulus (p^(n+4))) (p^3*k)*
        (Ring.inverse (Ideal.Quotient.mk (modulus (p^(n+4))) (3*d)))^2)=
      (norm (p^3):ℂ)*cubicThetaSymbolKloosterman (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(n+1))) h)
        (Ideal.Quotient.mk (modulus (p^(n+1))) k*
          (Ring.inverse (Ideal.Quotient.mk (modulus (p^(n+1))) (3*d)))^2) := by
    rw [map_mul,map_mul,mul_assoc,cubicThetaSymbolKloosterman_cubeInflation_residue hp]
    rw [map_mul,map_pow,cubicThetaResidueHom_inverse _ hi]
    simp only [residueReduction_mk]
  rw [cubicThetaKloostermanSum_factor (hu _) hd hd0 hdp.pow_right,
    cubicThetaKloostermanSum_factor (hu _) hd hd0 hdp.pow_right,
    hs (3*d) h3d,hs d hdp.symm,hl,
    cubicThetaFiniteKloosterman_cube_rescale hp hd hd0 hdp]
  ring

end CubicFirstMoment

end

end OAI
