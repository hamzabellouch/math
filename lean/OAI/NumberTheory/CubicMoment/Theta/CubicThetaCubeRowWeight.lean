import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedIdeal

namespace OAI

/-! The value of either signed cube row in canonical ideal coordinates. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_residue_units_associated {a b : Eisenstein} (h : Associated a b) :
    Nat.card (Residues a)ˣ=Nat.card (Residues b)ˣ := by
  have he : modulus a=modulus b := Ideal.span_singleton_eq_span_singleton.mpr h
  exact Nat.card_congr (Units.mapEquiv (Ideal.quotEquivOfEq he).toMulEquiv).toEquiv

lemma cubicTheta_normNat_neg (a : Eisenstein) : normNat (-a)=normNat a := by
  apply Nat.cast_injective (R:=ℝ)
  rw [normNat_cast,normNat_cast]
  simp only [norm,Eisenstein.coe_neg,Complex.normSq_neg]

lemma cubicThetaSignedCube_constant (ε : Bool) (ν : EisensteinIdealExponent)
    (hν : 0<ν cubicThetaRamifiedPrime) :
    cubicThetaEisensteinGaussCoefficient (cubicThetaSignedCube ε ν) 0=
      (3/2:ℂ)*(idealExponentNorm ν:ℂ)^2*(cubicThetaIdealTotient ν:ℂ) := by
  have h3 : (3:Eisenstein)∣(idealExponentGenerator ν)^3 :=
    cubicTheta_cube_row_three_iff.mpr ((cubicThetaRamifiedPrime_dvd_iff ν).mpr hν)
  cases ε
  · simpa only [cubicThetaSignedCube,Bool.false_eq_true,ite_false,
      idealExponentNorm,Complex.ofReal_natCast,cubicThetaIdealTotient] using
      cubicThetaEisenstein_constant_cube_totient (idealExponentGenerator_ne_zero ν) h3
  · have hneg : (-idealExponentGenerator ν)^3= -(idealExponentGenerator ν)^3 := by ring
    have he := cubicThetaEisenstein_constant_cube_totient
      (neg_ne_zero.mpr (idealExponentGenerator_ne_zero ν))
      (show (3:Eisenstein)∣(-idealExponentGenerator ν)^3 by rw [hneg]; exact dvd_neg.mpr h3)
    rw [hneg,cubicTheta_normNat_neg,cubicTheta_residue_units_associated
      (Associated.refl (idealExponentGenerator ν)).neg_left] at he
    simpa only [cubicThetaSignedCube,ite_true,idealExponentNorm,
      Complex.ofReal_natCast,cubicThetaIdealTotient] using he

end CubicFirstMoment

end

end OAI
