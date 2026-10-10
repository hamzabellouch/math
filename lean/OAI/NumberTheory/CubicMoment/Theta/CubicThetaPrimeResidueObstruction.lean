import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueImage

namespace OAI

/-! The critical local image condition is exactly the two missing
unramified residue identities. Neither identity is assumed here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCriticalGauss_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 1 h≠0 := by
  intro hz
  have he := cubicThetaPrimeAdditiveGauss_product hp h hh
  rw [hz,zero_mul] at he
  exact (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne') he.symm

lemma cubicThetaPrimeResidueVector_line_iff_cube {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p∣h) :
    (cubicThetaPrimeResidueVector p h 1=
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeResidueVector p h 0) ↔
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  have hc := hp.2.coprime_iff_not_dvd.mpr hh
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have hg := cubicThetaPrimeAdditiveGauss_product hp h hc
  have hG : cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ)≠0 :=
    div_ne_zero (cubicThetaPrimeCriticalGauss_ne_zero hp h hc) hq
  have he := cubicThetaArithmeticFourierResidue_primeHecke hp h hh
  rw [cubicThetaPrimeCubeFactor_pole hp,cubicThetaPrimeFirstFactor_critical hp h hc] at he
  have hidentity : cubicThetaArithmeticFourierResidue (p^3*h) (4/3)-
      cubicThetaArithmeticFourierResidue h (4/3)=
      -(cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ))*
        (cubicThetaPrimeResidueVector p h 1-
          (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeResidueVector p h 0) := by
    rw [he]
    simp only [cubicThetaPrimeResidueVector,Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp
    linear_combination -(cubicThetaArithmeticFourierResidue h (4/3))*hg
  conv_rhs => rw [←sub_eq_zero,hidentity]
  simp only [mul_eq_zero,neg_eq_zero,hG,false_or,sub_eq_zero]

theorem cubicThetaPrimeResidueImage_iff_identities {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p∣h) :
    (∃ v : Fin 3 → ℂ, (cubicThetaPrimeCriticalMatrix p hp h).mulVec v=
      cubicThetaPrimeResidueVector p h) ↔
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) ∧
      cubicThetaArithmeticFourierResidue (p^2*h) (4/3)=0 := by
  rw [cubicThetaPrimeCriticalMatrix_range_iff hp h (hp.2.coprime_iff_not_dvd.mpr hh),
    cubicThetaPrimeResidueVector_line_iff_cube hp h hh]
  apply and_congr Iff.rfl
  change (cubicThetaPrimeCriticalScale p)^2*cubicThetaArithmeticFourierResidue (p^2*h) (4/3)=0 ↔ _
  simp only [mul_eq_zero,pow_ne_zero 2 (cubicThetaPrimeCriticalScale_ne_zero hp),false_or]

end CubicFirstMoment

end

end OAI
