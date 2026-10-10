import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCharacter
import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorNoncube
import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof

namespace OAI

/-! Exact cube support of the constant coefficient of the cubic
Eisenstein series, including the ramified factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_constant_noncube {c : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c ≠ 0) (hcb : ¬∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0 = 0 := by
  obtain ⟨u,hu,hcu,hchi⟩ :=
    (cubicNumeratorChar_ne_one_iff cubicSupplementaryPeriodicity_proved c hc0).mp
      (cubicNumeratorChar_noncube cubicSupplementaryPeriodicity_proved hc0 hcb)
  exact cubicThetaEisenstein_constant_vanish hc hc0 hu hcu.of_mul_left_right hchi

lemma cubicThetaEisensteinWeight_cube {c : Eisenstein} (hcb : ∃ j : Eisenstein, j^3=c)
    (d : Eisenstein) :
    cubicThetaEisensteinWeight c d = if primary d ∧ IsCoprime c d then 1 else 0 := by
  unfold cubicThetaEisensteinWeight
  split_ifs with hd
  · obtain ⟨j,rfl⟩ := hcb
    have hdj : IsCoprime d j := hd.2.symm.of_isCoprime_of_dvd_right
      (dvd_pow_self j (by norm_num : (3:ℕ) ≠ 0))
    rw [cubicSymbol_pow_upper hd.1, cubicSymbol_cube_of_isCoprime hd.1 j hdj]
  · rfl

theorem cubicThetaEisenstein_constant_cube {c : Eisenstein}
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0 =
      ∑' x : Residues (3*c), if primary (residueRepresentative (3*c) x) ∧
        IsCoprime c (residueRepresentative (3*c) x) then (1:ℂ) else 0 := by
  unfold cubicThetaEisensteinGaussCoefficient cubicThetaEisensteinResidueWeight
  simp only [Eisenstein.coe_zero, zero_div, tracePair, mul_zero, Complex.zero_re,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  apply tsum_congr
  intro x
  exact cubicThetaEisensteinWeight_cube hcb _

end CubicFirstMoment

end

end OAI
