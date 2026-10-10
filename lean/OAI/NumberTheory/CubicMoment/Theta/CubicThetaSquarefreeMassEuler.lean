import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSquareDecomposition
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryMassEuler

namespace OAI

/-! The squarefree norm series is the quotient by the square factor.
Every primary element occurs exactly once. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaSquareNumerator_weight (t : ℝ) (cd : CubicThetaPrimaryPair) :
    (norm (cubicThetaSquareNumerator cd))^(-t) =
      (norm cd.val.1)^(-t) * (norm cd.val.2)^(-(2*t)) := by
  rw [cubicThetaSquareNumerator,norm_mul_eq,eisenstein_norm_pow,
    Real.mul_rpow (norm_nonneg _) (sq_nonneg _),←Real.rpow_natCast,
    ←Real.rpow_mul (norm_nonneg _)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(-t)=-(2*t) by ring]

theorem cubicThetaSquarefreeMass_mul {t : ℝ} (ht : 1 < t) :
    cubicThetaSquarefreeMass t * cubicThetaPrimaryMass (2*t)=cubicThetaPrimaryMass t := by
  have hc := cubicThetaSquarefreeMass_summable ht
  have hd := cubicThetaPrimaryMass_summable (show 1 < 2*t by linarith)
  symm
  calc
    cubicThetaPrimaryMass t = ∑' cd : CubicThetaPrimaryPair,
        (norm (cubicThetaSquareNumerator cd))^(-t) :=
      (cubicThetaSquareIndexEquiv.tsum_eq (fun d : PrimaryArgument => (norm d.val)^(-t))).symm
    _ = ∑' cd : CubicThetaPrimaryPair, (norm cd.val.1)^(-t) *
        (norm cd.val.2)^(-(2*t)) := tsum_congr (cubicThetaSquareNumerator_weight t)
    _ = ∑' cd : CubicThetaSquarefreePrimary × PrimaryArgument,
        (norm cd.1.val)^(-t) * (norm cd.2.val)^(-(2*t)) :=
      (cubicThetaMassPairEquiv.symm.tsum_eq _).symm
    _ = _ := (tsum_mul_tsum_of_summable_norm hc.norm hd.norm).symm

lemma cubicThetaSquarefreeMass_quotient {t : ℝ} (ht : 1 < t) :
    cubicThetaSquarefreeMass t=cubicThetaPrimaryMass t/cubicThetaPrimaryMass (2*t) := by
  apply (eq_div_iff (cubicThetaPrimaryMass_pos (by linarith : 1 < 2*t)).ne').mpr
  exact cubicThetaSquarefreeMass_mul ht

theorem cubicThetaCoefficientMass_primary_quotient {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaCoefficientMass σ =
      (6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
       2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹) *
      (cubicThetaPrimaryMass (1+σ)/cubicThetaPrimaryMass (2+2*σ)) *
      cubicThetaPrimaryMass (2+3*σ) := by
  rw [cubicThetaCoefficientMass_factorization hσ,
    cubicThetaSquarefreeMass_quotient (by linarith : 1 < 1+σ)]
  rw [show 2*(1+σ)=2+2*σ by ring]

end CubicFirstMoment

end

end OAI
