import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanResidue

namespace OAI

/-! A choice-free finite-ring formula for the arithmetic Gram phases. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaKloostermanSum_finite (h k : Eisenstein) {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) :
    cubicThetaKloostermanSum h k c hc=
      ∑' x : Residues (3*c),cubicThetaEisensteinResidueWeight c x*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0)
          (Ideal.Quotient.mk (modulus (3*c)) h*x+
            Ideal.Quotient.mk (modulus (3*c)) k*Ring.inverse x) := by
  classical
  unfold cubicThetaKloostermanSum
  apply tsum_congr
  intro x
  let d := residueRepresentative (3*c) x
  by_cases hd : primary d ∧ IsCoprime c d
  · let r : CubicThetaBottomRow := ⟨c,d,hc,hd.1,hd.2⟩
    have hU : (cubicThetaRowResidueUnit r:Residues (3*c))=x :=
      (cubicThetaRowResidueUnit_val r).trans (residueRepresentative_spec (3*c) x)
    have hI : (((cubicThetaRowResidueUnit r)⁻¹:(Residues (3*c))ˣ):Residues (3*c))=
        Ring.inverse x := by
      rw [←hU,Ring.inverse_unit]
    change cubicThetaKloostermanWeight h k c hc d=
      cubicThetaEisensteinWeight c d*_
    rw [cubicThetaKloostermanWeight,dite_eq_left hd,cubicThetaEisensteinWeight,ite_eq_left hd]
    have he := cubicThetaGramRowPhase_residue h k r hc0
    change cubicThetaGramRowPhase h k r=cubicSymbol d c*
      residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0)
        (Ideal.Quotient.mk (modulus (3*c)) h*(cubicThetaRowResidueUnit r:Residues (3*c))+
          Ideal.Quotient.mk (modulus (3*c)) k*
            (((cubicThetaRowResidueUnit r)⁻¹:(Residues (3*c))ˣ):Residues (3*c))) at he
    rw [hU,hI] at he
    exact he
  · change cubicThetaKloostermanWeight h k c hc d=cubicThetaEisensteinWeight c d*_
    rw [cubicThetaKloostermanWeight,dite_eq_right hd,cubicThetaEisensteinWeight,ite_eq_right hd,zero_mul]

end CubicFirstMoment

end

end OAI
